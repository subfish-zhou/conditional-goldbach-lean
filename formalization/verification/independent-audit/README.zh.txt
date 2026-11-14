Li–Liu 原始 TeX 独立审计

英文版：README.txt

report.html 展示原文与Lean对照、机械验证和数值待办。
summary.json 汇总数据，final-comparison.json 记录逐项比较结果。

本目录包含独立参考、表示桥梁和905直接枚举证书。
Challenge占位指定比较目标，Solution使用propext、Classical.choice、Quot.sound。

用 verify_project.py 生成当前构建记录后，在仓库根目录复跑。
  python3 formalization/verification/independent-audit/prepare_comparator.py
  python3 formalization/verification/independent-audit/run_comparator.py
  python3 formalization/scripts/refresh_audit_summary.py
  python3 formalization/verification/independent-audit/build_report.py
  node formalization/verification/independent-audit/test_report.cjs

数学审阅建立TeX与参考的对应，比较器核查参考与实际实现。
附录B剩余任务为特定积分误差、相应整数区间和有限矩阵数值范数认证。
905直接计数证书位于appendices/NumericCrossCheck.lean。
