Li–Liu 原始 TeX 独立审计

打开 report.html 查看中文／Lean 对照、机械结果、计时和仍未认证的数值主张。
summary.json 是汇总数据；comparator.log 和三个 control-*.log 是真实比较器日志。

主证明库保持冻结。本轮的审计参考、桥梁及905直接枚举证明位于本目录，
不由 LiLiuGoldbach.lean 导入。Challenge 中的 sorry 是比较目标的占位；
真实 Solution 必须仅依赖 propext、Classical.choice、Quot.sound。

复跑（在已有主工程及Mathlib/Goldbach依赖的环境中）：
  python3 formalization/verification/independent-audit/prepare_comparator.py
  python3 formalization/verification/independent-audit/run_comparator.py
  python3 formalization/verification/independent-audit/build_report.py
  node formalization/verification/independent-audit/test_report.cjs

run_comparator.py 设置 COMPARATOR_BWRAP 指向 bwrap_local_dependencies.py，
只为两个本地 Lake 路径依赖补充只读挂载；保留全部原有隔离选项与比较规则。
搬迁工程时须调整本地 goldbach 依赖路径。

编译计时：measure_build.py warm 测无改动复查；project-clean 在独立副本中
从头构建本项目，复用依赖缓存。若副本已有编译产物，脚本拒绝把它当作冷构建；
保留并移走旧 benchmark-project 后才能重复同一测量。压缩包不包含缓存和副本。

重要范围：TeX→独立参考仍是数学语义审查，comparator不解析TeX。
附录B原文的积分误差、数值谱界等尚未全部认证；新增905枚举证明不替代该积分路径。
