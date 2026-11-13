# 并行证明复核记录

`main-assembly-cross-check.json` 是所有证明模块定稿后的独立只读复核，记录当前源码哈希、主定理与谱字典拼接的条件检查、以及独立遍历的实际待证依赖。

其余模块报告是各工作分支交付时的验证记录，供追溯使用。全工程的最新计数、声明归属、传递公理和来源哈希统一以父目录的 `proof-status.json`、`reviewed-types.json`、`reviewed-definitions.json` 及 `verification.json` 为准。

`collectAxioms` 没有 `sorryAx` 表示该 Lean 声明的证明依赖已经闭合；不表示一个带有 GRH、S 或 R 假设的命题消除了这些假设。编译成功也不表示其余保留占位的论文内容已经证明。
