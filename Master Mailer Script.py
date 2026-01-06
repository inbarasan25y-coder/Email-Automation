#!/usr/bin/env python3

"""
Master Mailer Script (Multi-Format Edition)
Multi-threaded email sender with random delays within batches.
Supports 3 formatting options: Mixed Themes, Fixed Verdana, Plain Text
Auto-blocks senders that hit daily limit to prevent account blocking.
Respects unsubscribe requests - skips sending to opted-out recipients.
"""

import csv
import smtplib
import time
import random
import threading
import sys
import os
import re
from email.message import EmailMessage
from datetime import datetime
from typing import List, Dict, Tuple, Callable, Any, Set

# === CONFIGURATION ===
DEFAULT_INPUT_CSV_FILE = 'mailer_data.csv'
BATCH_SIZE = 164
MIN_WAIT_SECONDS = 180  # Wait between batches
MAX_WAIT_SECONDS = 280
MIN_EMAIL_DELAY = 1 # Random delay before each email sends (within batch)
MAX_EMAIL_DELAY = 9

LOG_HEADERS = [
    'Sender Name', 'Sender Email', 'Recipient Name', 'Recipient Company',
    'Recipient Email', 'Subject Line', 'Pitch', 'Sign-Off Phrase',
    'Sender Title', 'End Line', 'Unsubscribe', 'Status', 'Error Type', 'Date Sent', 'Time Sent'
]

LOG_LOCK = threading.Lock()
BLOCKED_SENDERS_LOCK = threading.Lock()
CsvRow = Dict[str, str]

# Global format settings
FORMAT_OPTION = 1  # 1=Mixed Themes, 2=Fixed Verdana, 3=Plain Text

# Track blocked senders
BLOCKED_SENDERS: Set[str] = set()

# Font configurations for Option 1 (Mixed Themes)
MIXED_THEME_FONTS = [
    ('Aptos', '12pt', '#000000'),
    ('Cambria', '11pt', '#000066'),
    ('Segoe UI', '11pt', '#002060'),
    ('Arial Nova', '12pt', '#000000'),
    ('Aptos Display', '11pt', '#000066'),
    ('Calibri', '11pt', '#002060'),
    ('Grandview', '12pt', '#000000'),
    ('Nirmala UI', '11pt', '#000066'),
    ('Georgia', '11pt', '#002060'),
    ('Open Sans', '12pt', '#000000'),
    ('Roboto', '11pt', '#000066'),
    ('Roboto Condensed', '12pt', '#002060'),
    ('Rockwell', '11pt', '#000000'),
    ('Sitka Display', '12pt', '#000066'),
    ('Times New Roman', '11pt', '#002060'),
    ('Trebuchet MS', '11pt', '#000000'),
    ('Univers', '10pt', '#000066'),
    ('Verdana', '9pt', '#002060'),
    ('Verdana Pro Cond', '9pt', '#000000'),
]

# Counter for cycling through fonts
FONT_COUNTER = 0
FONT_LOCK = threading.Lock()

def get_next_font_style() -> Tuple[str, str, str]:
    """Get the next font style in rotation (for Option 1)."""
    global FONT_COUNTER
    with FONT_LOCK:
        font, size, color = MIXED_THEME_FONTS[FONT_COUNTER % len(MIXED_THEME_FONTS)]
        FONT_COUNTER += 1
    return font, size, color

# === UTILITIES ===

def is_unsubscribed(row_data: CsvRow) -> bool:
    """Check if recipient has unsubscribed (opted out)."""
    unsubscribe_value = row_data.get('Unsubscribe', '').strip().lower()
    # Check for common opt-out indicators
    opt_out_keywords = ['remove', 'unsubscribe', 'opt-out', 'opt out', 'stop', 'yes', 'true', 'x']
    return unsubscribe_value in opt_out_keywords

def clean_and_format_text(text: str) -> str:
    """Clean and format text by replacing escape sequences and quotes."""
    if not text:
        return ""
    text = text.replace('\\n', '\n')
    text = text.replace(''', "'").replace(''', "'")
    text = text.replace('"', '"').replace('"', '"')
    return text

def apply_bold_formatting(text: str) -> Tuple[str, str]:
    """Convert **text** to plain text and HTML bold formatting."""
    plain = re.sub(r'\*\*(.*?)\*\*', r'\1', text)
    html = re.sub(r'\*\*(.*?)\*\*', r'<b>\1</b>', text.replace('\n', '<br>'))
    return plain, html

def replace_placeholders(text: str, row_data: CsvRow) -> str:
    """
    Replace all placeholders in text with corresponding CSV column values.
    Supports formats: [Column Name], {Column Name}, {{Column Name}}
    Case-insensitive matching.
    """
    if not text or not row_data:
        return text

    result_text = text

    # Replace placeholders with CSV column values
    for column, value in row_data.items():
        if column and value is not None:
            clean_value = str(value).strip()

            # Handle different placeholder formats and cases
            placeholders = [
                f'[{column}]',
                f'{{{column}}}',
                f'{{{{{column}}}}}',
                f'[{column.upper()}]',
                f'{{{column.upper()}}}',
                f'{{{{{column.upper()}}}}}',
                f'[{column.lower()}]',
                f'{{{column.lower()}}}',
                f'{{{{{column.lower()}}}}}',
                f'[{column.title()}]',
                f'{{{column.title()}}}',
                f'{{{{{column.title()}}}}}',
            ]

            for placeholder in placeholders:
                result_text = result_text.replace(placeholder, clean_value)

    return result_text

def parse_smtp_error(error_str: str) -> str:
    """Extract and clean SMTP error message."""
    error_msg = str(error_str).strip()

    # Check for daily limit errors
    if '5.4.5' in error_msg or 'Daily user sending limit' in error_msg:
        return 'Daily Sending Limit Exceeded'
    if '5.5.1' in error_msg or 'Authentication failed' in error_msg or 'Invalid credentials' in error_msg:
        return 'Authentication Failed'
    if '5.1.1' in error_msg or 'Bad email address' in error_msg:
        return 'Invalid Email Address'
    if 'SMTPRecipientsRefused' in error_msg:
        return 'Recipient Refused'
    if 'SMTPServerDisconnected' in error_msg:
        return 'Server Disconnected'
    if 'connection timed out' in error_msg.lower():
        return 'Connection Timeout'
    if 'rate limit' in error_msg.lower():
        return 'Rate Limited'

    # Truncate long error messages
    if len(error_msg) > 80:
        return error_msg[:80] + "..."
    return error_msg

def _send_email(msg: EmailMessage, sender_email: str, smtp_pass: str) -> Tuple[str, str]:
    """Send email via Gmail SMTP and return (status, error_type)."""
    error_type = ""

    try:
        with smtplib.SMTP_SSL('smtp.gmail.com', 465) as smtp:
            smtp.login(sender_email, smtp_pass)
            smtp.send_message(msg)
        return 'Sent', ''
    except smtplib.SMTPAuthenticationError as e:
        error_type = 'Authentication Failed'
        return f'Failed: {error_type}', error_type
    except smtplib.SMTPRecipientsRefused as e:
        error_type = 'Recipient Refused'
        return f'Failed: {error_type}', error_type
    except smtplib.SMTPServerDisconnected as e:
        error_type = 'Server Disconnected'
        return f'Failed: {error_type}', error_type
    except smtplib.SMTPException as e:
        error_msg = str(e)
        error_type = parse_smtp_error(error_msg)
        return f'Failed: {error_type}', error_type
    except Exception as e:
        error_msg = str(e)
        error_type = parse_smtp_error(error_msg)
        return f'Failed: {error_type}', error_type

# === MESSAGE BUILDERS ===

def build_first_touch_message(row_data: CsvRow, font_style: Tuple[str, str, str] = None) -> EmailMessage:
    """Build first touch email message with selectable format."""
    sender_name = clean_and_format_text(row_data.get('Sender Name', '').strip())
    sender_email = row_data.get('Sender Email', '').strip()
    recipient_email = row_data.get('Recipient Email', '').strip()
    subject_raw = clean_and_format_text(row_data.get('Subject Line', '').strip())
    pitch_raw = clean_and_format_text(row_data.get('Pitch', '').strip())
    sign_off = clean_and_format_text(row_data.get('Sign-Off Phrase', '').strip())
    sender_title = clean_and_format_text(row_data.get('Sender Title', '').strip())
    end_line = clean_and_format_text(row_data.get('End Line', '').strip())

    subject = replace_placeholders(subject_raw, row_data)
    pitch_text = replace_placeholders(pitch_raw, row_data)

    plain, html = apply_bold_formatting(pitch_text)

    plain_msg = f"""{plain}

{sign_off}
{sender_name}
{sender_title}

{end_line}
""".strip()

    msg = EmailMessage()
    msg['Subject'] = subject
    msg['From'] = f'"{sender_name}" <{sender_email}>'
    msg['To'] = recipient_email
    msg.set_content(plain_msg)

    if FORMAT_OPTION == 1:  # Mixed Themes
        font_family, font_size, color = font_style if font_style else get_next_font_style()
        html_msg = f"""
    <html>
      <body style="font-family: {font_family}, sans-serif; font-size: {font_size}; color: {color}; margin: 0; padding: 0;">
        <div>{html}</div>
        <br>
        <div>
          {sign_off}<br>
          <b>{sender_name}</b><br>
          {sender_title}
        </div>
        <br>
        <div style="font-size: 7pt; color: {color};">
          {end_line}
        </div>
      </body>
    </html>
    """
        msg.add_alternative(html_msg.strip(), subtype='html')

    elif FORMAT_OPTION == 2:  # Fixed Verdana
        html_msg = f"""
    <html>
      <body style="font-family: Verdana, sans-serif; font-size: 9pt; color: #000066; margin: 0; padding: 0;">
        <div>{html}</div>
        <br>
        <div>
          {sign_off}<br>
          <b>{sender_name}</b><br>
          {sender_title}
        </div>
        <br>
        <div style="font-size: 7pt; color: #000066;">
          {end_line}
        </div>
      </body>
    </html>
    """
        msg.add_alternative(html_msg.strip(), subtype='html')

    # FORMAT_OPTION == 3 (Plain Text) - no HTML alternative added

    return msg

def build_followup_message(row_data: CsvRow, font_style: Tuple[str, str, str] = None) -> EmailMessage:
    """Build follow-up email message with selectable format."""
    sender_name = clean_and_format_text(row_data.get('Sender Name', '').strip())
    sender_first = sender_name.split()[0] if sender_name else ''
    sender_email = row_data.get('Sender Email', '').strip()
    recipient_name = clean_and_format_text(row_data.get('Recipient Name', '').strip())
    recipient_email = row_data.get('Recipient Email', '').strip()
    subject_raw = clean_and_format_text(row_data.get('Subject Line', '').strip())
    pitch_raw = clean_and_format_text(row_data.get('Pitch', '').strip())
    sign_off = clean_and_format_text(row_data.get('Sign-Off Phrase', '').strip())
    sender_title = clean_and_format_text(row_data.get('Sender Title', '').strip())
    end_line = clean_and_format_text(row_data.get('End Line', '').strip())
    sent_date = clean_and_format_text(row_data.get('Date Sent', '').strip())

    subject = replace_placeholders(subject_raw, row_data)
    pitch_text = replace_placeholders(pitch_raw, row_data)

    plain_orig, html_orig = apply_bold_formatting(pitch_text)

    plain_followup = f"""Hi {recipient_name},

Just a gentle follow-up on my last email. Please let me know if there's anything more I can provide.

Happy to share counts & Cost if useful.

Regards,
{sender_first}"""

    plain_signature = f"{sign_off}\n{sender_name}\n{sender_title}\n\n{end_line}"

    final_plain = f"""{plain_followup}

_______________________________________________________________________________________________________
From: {sender_name} <{sender_email}>
Sent: {sent_date}
To: {recipient_name} <{recipient_email}>
Subject: {subject}

{plain_orig}

{plain_signature}"""

    msg = EmailMessage()
    msg['Subject'] = f"RE: {subject}"
    msg['From'] = f'"{sender_name}" <{sender_email}>'
    msg['To'] = recipient_email
    msg.set_content(final_plain)

    if FORMAT_OPTION == 1:  # Mixed Themes
        font_family, font_size, color = font_style if font_style else get_next_font_style()

        html_followup = f"""
        <div style="font-family: {font_family}, sans-serif; font-size: {font_size}; color: {color};">
          <p>Dear <b>{recipient_name}</b>,<br>
          <br>
          I am Curious to know if you had chance to review my previous email?<br>
          <br>
          Can I share you the <b>counts</b> and <b>cost details</b> for your review to make a decision?<br>
          <br>
          Looking forward to your response.<br>
          <br>
          Regards,<br>
          <b>{sender_first}</b></p>

        </div>"""

        html_signature_section = f"""
          <div style="font-family: {font_family}, sans-serif; font-size: {font_size}; color: {color};">
            <div>{html_orig}</div>
            <br>
            <div>
              {sign_off}<br>
              <b>{sender_name}</b><br>
              {sender_title}
            </div>
            <br>
            <div style="font-size: 7pt; color: {color};">
              {end_line}
            </div>
          </div>"""

        final_html = f"""
    <html>
      <body style="margin: 0; padding: 0;">
        {html_followup}

        <div style="border: none; border-top: solid #E1E1E1 1.0pt; margin: 15px 0; padding-top: 10px;">
          <div style="font-family: Calibri, sans-serif; font-size: 11pt; color: black; line-height: 1.2;">
            <b>From:</b> {sender_name} &lt;{sender_email}&gt;<br>
            <b>Sent:</b> {sent_date}<br>
            <b>To:</b> {recipient_name} &lt;{recipient_email}&gt;<br>
            <b>Subject:</b> {subject}
          </div>
          <br>
          {html_signature_section}
        </div>
      </body>
    </html>
    """
        msg.add_alternative(final_html.strip(), subtype='html')

    elif FORMAT_OPTION == 2:  # Fixed Verdana
        html_followup = f"""
        <div style="font-family: Verdana, sans-serif; font-size: 9pt; color: #000066;">
          <p>Hi {recipient_name},</p>
          <p>I wanted to follow up to see if you'd like more details on the verified data we provide. It could help you reach the right decision-makers efficiently.</p>
          <p>Happy to share <b>counts & Cost</b> if useful.</p>
          <p>Best,<br><b>{sender_first}</b></p>
        </div>"""

        html_signature_section = f"""
          <div style="font-family: Verdana, sans-serif; font-size: 9pt; color: #000066;">
            <div>{html_orig}</div>
            <br>
            <div>
              {sign_off}<br>
              <b>{sender_name}</b><br>
              {sender_title}
            </div>
            <br>
            <div style="font-size: 7pt; color: #000066;">
              {end_line}
            </div>
          </div>"""

        final_html = f"""
    <html>
      <body style="margin: 0; padding: 0;">
        {html_followup}

        <div style="border: none; border-top: solid #E1E1E1 1.0pt; margin: 15px 0; padding-top: 10px;">
          <div style="font-family: Calibri, sans-serif; font-size: 11pt; color: black; line-height: 1.2;">
            <b>From:</b> {sender_name} &lt;{sender_email}&gt;<br>
            <b>Sent:</b> {sent_date}<br>
            <b>To:</b> {recipient_name} &lt;{recipient_email}&gt;<br>
            <b>Subject:</b> {subject}
          </div>
          <br>
          {html_signature_section}
        </div>
      </body>
    </html>
    """
        msg.add_alternative(final_html.strip(), subtype='html')

    # FORMAT_OPTION == 3 (Plain Text) - no HTML alternative added

    return msg

# === CAMPAIGN ENGINE ===

MessageBuilder = Callable[[CsvRow, Tuple[str, str, str]], EmailMessage]

def is_sender_blocked(sender_email: str) -> bool:
    """Check if sender is blocked."""
    with BLOCKED_SENDERS_LOCK:
        return sender_email.lower() in BLOCKED_SENDERS

def block_sender(sender_email: str):
    """Block a sender to prevent further sending."""
    with BLOCKED_SENDERS_LOCK:
        BLOCKED_SENDERS.add(sender_email.lower())

def _process_and_send_task(row_data: CsvRow, log_writer: Any, campaign_name: str, message_builder: MessageBuilder):
    """Process and send a single email task with random initial delay."""
    sender_email = row_data.get('Sender Email', '').strip()
    recipient_email = row_data.get('Recipient Email', 'N/A')

    # Check if recipient has unsubscribed (opted out)
    if is_unsubscribed(row_data):
        print(f"🚫 [{campaign_name}] OPTED-OUT: {recipient_email} - Respecting unsubscribe request")

        log_data = {key: "N/A" for key in LOG_HEADERS}
        for key in row_data:
            if key in log_data:
                log_data[key] = str(row_data[key]).strip()
        log_data['Status'] = 'Skipped'
        log_data['Error Type'] = 'Unsubscribed/Opted-Out'

        with LOG_LOCK:
            now = datetime.now()
            log_data['Date Sent'] = now.strftime('%Y-%m-%d')
            log_data['Time Sent'] = now.strftime('%H:%M:%S')
            log_writer.writerow([log_data.get(h, "N/A") for h in LOG_HEADERS])
        return

    # Check if sender is already blocked
    if is_sender_blocked(sender_email):
        # Skip this email - sender is blocked
        print(f"⏭️  [{campaign_name}] Skipping {recipient_email} - Sender {sender_email} is BLOCKED")

        log_data = {key: "N/A" for key in LOG_HEADERS}
        for key in row_data:
            if key in log_data:
                log_data[key] = str(row_data[key]).strip()
        log_data['Status'] = 'Skipped'
        log_data['Error Type'] = 'Sender Blocked'

        with LOG_LOCK:
            now = datetime.now()
            log_data['Date Sent'] = now.strftime('%Y-%m-%d')
            log_data['Time Sent'] = now.strftime('%H:%M:%S')
            log_writer.writerow([log_data.get(h, "N/A") for h in LOG_HEADERS])
        return

    # Get font style for this email (only used for Option 1)
    font_style = get_next_font_style() if FORMAT_OPTION == 1 else None

    # Each thread waits a random amount before sending
    delay = random.randint(MIN_EMAIL_DELAY, MAX_EMAIL_DELAY)

    print(f"⏱️  [{campaign_name}] Scheduling {recipient_email} to send in {delay}s")
    time.sleep(delay)

    # Initialize log data
    log_data = {key: "N/A" for key in LOG_HEADERS}

    try:
        # Fill log data from row
        for key in row_data:
            if key in log_data:
                log_data[key] = str(row_data[key]).strip()

        # Build and send message
        msg = message_builder(row_data, font_style)
        log_data['Subject Line'] = msg['Subject']

        smtp_pass = row_data.get('Email Password', '').strip()
        if not smtp_pass:
            raise ValueError("Email Password not found in CSV")

        status, error_type = _send_email(msg, sender_email, smtp_pass)
        log_data['Status'] = status
        log_data['Error Type'] = error_type

        # Check for daily sending limit error
        if 'Daily Sending Limit Exceeded' in status:
            block_sender(sender_email)
            print(f"🚫 [{campaign_name}] SENDER BLOCKED: {sender_email} - Daily limit reached!")
            print(f"   └─ All remaining emails from this sender will be skipped")

        # Print status
        if status == 'Sent':
            print(f"✅ [{campaign_name}] {status} to {log_data['Recipient Email']} from {log_data['Sender Email']} (after {delay}s)")
        else:
            error_display = error_type if error_type else status.replace('Failed: ', '')
            print(f"❌ [{campaign_name}] ERROR: {error_display}")
            print(f"   └─ Sender: {log_data['Sender Email']} | Recipient: {log_data['Recipient Email']}")

    except Exception as e:
        error_msg = str(e)[:100]
        log_data['Status'] = f'Failed: {error_msg}'
        log_data['Error Type'] = parse_smtp_error(error_msg)
        print(f"❌ [{campaign_name}] ERROR: {str(e)[:50]}")
        print(f"   └─ Sender: {log_data.get('Sender Email', 'Unknown')} | Recipient: {log_data.get('Recipient Email', 'Unknown')}")

    # Write to log file
    with LOG_LOCK:
        now = datetime.now()
        log_data['Date Sent'] = now.strftime('%Y-%m-%d')
        log_data['Time Sent'] = now.strftime('%H:%M:%S')
        log_writer.writerow([log_data.get(h, "N/A") for h in LOG_HEADERS])

def run_campaign(all_tasks: List[CsvRow], log_writer: Any, campaign_name: str, message_builder: MessageBuilder):
    """Run email campaign with batching and random staggered sending."""
    print(f"\n--- STARTING {campaign_name.upper()} CAMPAIGN ---")

    deferred_tasks: List[CsvRow] = []
    total_batches = (len(all_tasks) + BATCH_SIZE - 1) // BATCH_SIZE

    for i in range(0, len(all_tasks), BATCH_SIZE):
        batch = all_tasks[i:i + BATCH_SIZE]
        batch_num = i // BATCH_SIZE + 1

        # Ensure unique senders per batch
        batch_to_send, senders = [], set()
        for row in batch:
            sender = row.get('Sender Email', '').strip().lower()
            if sender and sender not in senders:
                batch_to_send.append(row)
                senders.add(sender)
            else:
                deferred_tasks.append(row)

        if not batch_to_send:
            print(f"⏭️  Skipping Batch {batch_num}/{total_batches} (no unique senders)")
            continue

        print(f"\n🚀 Batch {batch_num}/{total_batches} - Launching {len(batch_to_send)} emails")
        print(f"   Each email will send after a random {MIN_EMAIL_DELAY}-{MAX_EMAIL_DELAY}s delay")

        # Create all threads
        threads = [
            threading.Thread(
                target=_process_and_send_task,
                args=(row, log_writer, campaign_name, message_builder),
                daemon=True
            )
            for row in batch_to_send
        ]

        # Start all threads simultaneously (they each have random internal delays)
        batch_start = time.time()
        for thread in threads:
            thread.start()

        # Wait for all threads to complete
        for thread in threads:
            thread.join(timeout=300)

        batch_duration = int(time.time() - batch_start)
        print(f"✅ Batch {batch_num}/{total_batches} complete! (took {batch_duration}s)")

        # Wait between batches
        if i + BATCH_SIZE < len(all_tasks) or deferred_tasks:
            wait_time = random.randint(MIN_WAIT_SECONDS, MAX_WAIT_SECONDS)
            print(f"\n⏳ Waiting {wait_time}s before next batch...")
            time.sleep(wait_time)

    # Handle deferred tasks
    if deferred_tasks:
        print(f"\n--- CLEANUP PHASE: {len(deferred_tasks)} Deferred Emails ---")
        run_campaign(deferred_tasks, log_writer, campaign_name, message_builder)
    else:
        print("\n✅ No deferred emails remaining.")

def print_available_columns(csv_path: str):
    """Print available columns from CSV for user reference."""
    try:
        with open(csv_path, 'r', encoding='utf-8', errors='replace') as f:
            reader = csv.DictReader(f)
            columns = reader.fieldnames or []

        if columns:
            print(f"\n📋 Available columns in your CSV ({len(columns)} total):")
            for i, col in enumerate(columns, 1):
                print(f"  {i:2d}. {col}")

            print("\n💡 Placeholder Usage Examples:")
            print("   Formats: [Column Name], {Column Name}, {{Column Name}}")
            print("   Case-insensitive: [first name] = [First Name] = [FIRST NAME]")
            print("   In Subject: 'Hello [Recipient Name]' → 'Hello John Smith'")
            print("   In Pitch: 'Dear {recipient name}' → 'Dear John Smith'")

            print("\n🚫 Unsubscribe Feature:")
            print("   Column: 'Unsubscribe'")
            print("   To opt-out, enter: remove, unsubscribe, opt-out, stop, yes, or x")
            print("   Opted-out recipients will be skipped automatically")
        else:
            print("⚠️  No columns found in CSV file.")

    except Exception as e:
        print(f"⚠️  Could not read CSV columns: {e}")

def validate_csv_data(tasks: List[CsvRow]) -> Tuple[bool, List[str]]:
    """Validate CSV data for required fields."""
    errors = []
    required_fields = ['Sender Email', 'Recipient Email', 'Email Password']

    for i, row in enumerate(tasks, 1):
        for field in required_fields:
            if not row.get(field, '').strip():
                errors.append(f"Row {i}: Missing {field}")

    return len(errors) == 0, errors

# === MAIN ENTRY ===

def main():
    """Main entry point for the Master Mailer application."""
    global FORMAT_OPTION

    print("📧 Master Mailer - Multi-Format Edition (With Unsubscribe Support)")
    print("=" * 70)

    # Get CSV file path
    while True:
        csv_path = input(f"\nEnter CSV file path (default: {DEFAULT_INPUT_CSV_FILE}): ").strip()
        if not csv_path:
            csv_path = DEFAULT_INPUT_CSV_FILE

        if os.path.exists(csv_path):
            print(f"✅ Found file: {csv_path}")
            break
        print(f"🚨 File not found: {csv_path}")

    # Show available columns
    print_available_columns(csv_path)

    # Get email format choice
    while True:
        print("\n📝 Select Email Format:")
        print("1 - Mixed Theme Fonts (Aptos, Cambria, Segoe UI, etc. with rotating colors)")
        print("2 - Fixed Verdana Theme (Verdana 9pt, #000066)")
        print("3 - Plain Text Only")
        format_choice = input("Enter your choice (1, 2, or 3): ").strip()

        if format_choice in ('1', '2', '3'):
            FORMAT_OPTION = int(format_choice)
            format_names = {
                1: "Mixed Theme Fonts (19 fonts rotating)",
                2: "Fixed Verdana Theme (Verdana 9pt, #000066)",
                3: "Plain Text Only"
            }
            print(f"✅ Selected: {format_names[FORMAT_OPTION]}")
            break
        print("❌ Invalid option. Please enter 1, 2, or 3.")

    # Get campaign choice
    while True:
        print("\n📧 Select Campaign Type:")
        print("1 - First Touch Email")
        print("2 - Follow-up Email")
        choice = input("Enter your choice (1 or 2): ").strip()

        if choice in ('1', '2'):
            break
        print("❌ Invalid option. Please enter 1 or 2.")

    campaign = 'First Touch' if choice == '1' else 'Follow-up'
    message_builder = build_first_touch_message if choice == '1' else build_followup_message
    log_filename = f"sent_log_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv"

    # Load and validate CSV data
    try:
        with open(csv_path, 'r', encoding='utf-8', errors='replace') as f:
            tasks = list(csv.DictReader(f))

        if not tasks:
            print("❌ Empty CSV file. Exiting.")
            return

        print(f"\n✅ Loaded {len(tasks)} rows from CSV")

        # Validate data
        is_valid, errors = validate_csv_data(tasks)
        if not is_valid:
            print("❌ Data validation errors:")
            for error in errors[:10]:
                print(f"   {error}")
            if len(errors) > 10:
                print(f"   ... and {len(errors) - 10} more errors")
            return

        # Count opted-out recipients
        opted_out_count = sum(1 for task in tasks if is_unsubscribed(task))
        if opted_out_count > 0:
            print(f"\n🚫 Found {opted_out_count} opted-out recipient(s) that will be skipped")

    except Exception as e:
        print(f"🚨 Error reading CSV file: {e}")
        return

    # Show preview
    if tasks:
        print("\n🔍 Preview of placeholder replacement (first row):")
        sample_row = tasks[0]
        sample_subject = sample_row.get('Subject Line', '')
        sample_pitch = sample_row.get('Pitch', '')

        if sample_subject:
            replaced_subject = replace_placeholders(sample_subject, sample_row)
            print(f"   Subject: {sample_subject}")
            print(f"         → {replaced_subject}")

        if sample_pitch:
            pitch_preview = sample_pitch[:200] + "..." if len(sample_pitch) > 200 else sample_pitch
            replaced_pitch = replace_placeholders(pitch_preview, sample_row)
            print(f"   Pitch: {pitch_preview}")
            print(f"       → {replaced_pitch}")

    # Calculate estimated time
    max_delay_in_batch = MAX_EMAIL_DELAY
    active_emails = len(tasks) - opted_out_count
    num_batches = (active_emails + BATCH_SIZE - 1) // BATCH_SIZE
    estimated_between_batches = (num_batches - 1) * ((MIN_WAIT_SECONDS + MAX_WAIT_SECONDS) / 2)
    total_estimated_seconds = (num_batches * max_delay_in_batch) + estimated_between_batches
    estimated_minutes = int(total_estimated_seconds / 60)

    # Final confirmation
    format_names = {
        1: "Mixed Theme Fonts",
        2: "Fixed Verdana (9pt, #000066)",
        3: "Plain Text Only"
    }

    print(f"\n🎯 Campaign Summary:")
    print(f"   Type: {campaign}")
    print(f"   Format: {format_names[FORMAT_OPTION]}")
    print(f"   Total emails: {len(tasks)}")
    if opted_out_count > 0:
        print(f"   Opted-out (will skip): {opted_out_count}")
        print(f"   Active emails to send: {active_emails}")
    print(f"   Batch size: {BATCH_SIZE}")
    print(f"   Random delay per email: {MIN_EMAIL_DELAY}-{MAX_EMAIL_DELAY}s")
    print(f"   Wait between batches: {MIN_WAIT_SECONDS}-{MAX_WAIT_SECONDS}s")
    print(f"   Estimated time: ~{estimated_minutes} minutes")
    print(f"   Log file: {log_filename}")

    confirm = input(f"\n▶️  Proceed to send {active_emails} emails? (y/N): ").strip().lower()
    if confirm != 'y':
        print("❌ Campaign cancelled by user.")
        return

    # Run campaign
    try:
        with open(log_filename, 'w', newline='', encoding='utf-8') as logfile:
            writer = csv.writer(logfile)
            writer.writerow(LOG_HEADERS)

            start_time = datetime.now()
            run_campaign(tasks, writer, campaign, message_builder)
            end_time = datetime.now()

            print(f"\n🎉 Campaign Complete!")
            print(f"   Duration: {end_time - start_time}")
            print(f"   Log file: {log_filename}")

            if BLOCKED_SENDERS:
                print(f"\n⚠️  Blocked Senders ({len(BLOCKED_SENDERS)}):")
                for sender in sorted(BLOCKED_SENDERS):
                    print(f"   - {sender}")

    except KeyboardInterrupt:
        print(f"\n⚠️  Campaign interrupted by user. Partial results saved in: {log_filename}")
        if BLOCKED_SENDERS:
            print(f"\n⚠️  Blocked Senders ({len(BLOCKED_SENDERS)}):")
            for sender in sorted(BLOCKED_SENDERS):
                print(f"   - {sender}")
    except Exception as e:
        print(f"\n❌ Campaign error: {e}")
        print(f"   Partial results may be saved in: {log_filename}")

if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        print("\n👋 Goodbye!")
        sys.exit(0)
    except Exception as e:
        print(f"\n💥 Unexpected error: {e}")
        sys.exit(1)
