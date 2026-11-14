Independent audit of the original Li–Liu TeX

Chinese version: README.zh.txt

Open report.html for the source/Lean comparison, mechanical results, timings,
and remaining numerical work. summary.json contains aggregate data;
comparator.log and the three control-*.log files record comparator runs.

The independent references, representation bridges, and direct 905 counting
certificate are in this directory. Challenge placeholders specify comparison
targets. Solutions use only propext, Classical.choice, and Quot.sound.

Run from the repository root with a current build record from verify_project.py:
  python3 formalization/verification/independent-audit/prepare_comparator.py
  python3 formalization/verification/independent-audit/run_comparator.py
  python3 formalization/scripts/refresh_audit_summary.py
  python3 formalization/verification/independent-audit/build_report.py
  node formalization/verification/independent-audit/test_report.cjs

The comparator uses bubblewrap for isolation and resolves the pinned Lake
dependencies through the project's dependency configuration.

measure_build.py warm measures an unchanged rebuild. project-clean builds the
project in a separate copy while reusing dependency caches. A project-clean
measurement requires a copy without previously compiled project artifacts.

Mathematical review connects TeX to the independent reference; the comparator
checks the reference against the implementation. Remaining Appendix B work
includes certified integral-error inputs, the resulting concrete integer
interval, and numerical bounds for the finite spectral matrix. The direct
905 enumeration certificate is available in appendices/NumericCrossCheck.lean.
