"""Render and browser-check both languages, then bind the release evidence."""
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    commands = [['python3', 'scripts/write_progress_report.py']]
    for language in ('en', 'zh'):
        commands.extend([
            ['python3', 'scripts/build_progress.py', '--lang', language],
            ['node', 'scripts/test_progress.cjs', '--lang', language],
            ['python3', 'verification/independent-audit/build_report.py', '--lang', language],
            ['node', 'verification/independent-audit/test_report.cjs', '--lang', language],
        ])
    commands.append(['python3', 'scripts/update_verification.py'])
    for command in commands:
        print(' '.join(command), flush=True)
        subprocess.run(command, cwd=ROOT, env=os.environ, check=True)


if __name__ == '__main__':
    main()
