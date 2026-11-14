# 开发检查与公开接口

[English](development.md)

以下命令在 `formalization/` 中运行。Lean、Mathlib 与数论依赖继续使用固定版本。

## 日常检查

```bash
python3 scripts/check_project.py
```

Lake 增量构建修改过的模块及其依赖者，将 warning 视为失败。随后检查源码可达性、
局部编译选项、导入消费者、171 个定义体、102 个审阅定理类型、公开接口及所有本地
编译常量的传递公理。结果写入独立的 `.lake/development-check-*` 目录，明确标记为
`development`，不会覆盖发布证据。

添加 `--reuse-release` 时，先核对已有完整发布证据的源码、策略、工具、依赖和输出哈希。
全部一致才能复用；证据过期则执行日常检查。日常检查结果不会被标记为完成独立比较。

## 完整发布验证

Linux 下安装 `bubblewrap`，然后运行：

```bash
python3 -m pip install -r requirements-review.txt
npm ci
npx playwright install chromium
python3 scripts/verify_project.py
python3 scripts/render_verified.py
python3 scripts/test_verification.py
python3 scripts/package_verified.py
```

完整流程保留 218 项 Comparator、103 条独立完整类型检查和三类故意改坏的对照，
同时执行全库构建、公开接口及依赖审计。沙箱适配器分别记录依赖解析、构建、导出及
内核子进程耗时，保持原有挂载、环境清理、命名空间和父进程退出时终止的行为。
阶段日志的哈希纳入验证记录；父进程中的比较耗时仍计入总耗时。

`render_verified.py` 生成并检查中英文报告，再汇总发布证据。浏览器检查包括所有
声明范围中的逐字源码、LaTeX、首次加载深链接、移动端宽度及无网络使用。

GitHub 工作流在 PR 上运行日常检查，在 `main` 推送和手动触发时执行完整发布验证。
Actions 固定到提交哈希，并上传结果或失败日志。生成材料回写分支仍是明确的 Git 操作。

## 接口约定

`reference/public-api.json` 固定了 `cb16bfc` 的 1,621 个公开源码声明。检查器将 universe
参数按位置统一命名、去除表达式元数据和编译器自动生成的参数卫生作用域（其中含源文件路径），
然后比较完整类型结构；显式参数名、顺序、隐式性、
域与结论都参与比较。该检查比定义等同性更严格，与面向论文的 Comparator 配合使用。
可以新增声明；修改已有接口需要明确的兼容性决策，不能通过重新生成基线自动接受。

旧模块路径和声明名通过兼容导入或包装继续可用。仅供证明使用的 tactic 导入设为私有，
下游应显式导入所用 tactic。主库禁止文件级 heartbeat、递归深度和透明度覆盖；确有必要
的例外应局限于单条声明，并说明测量依据。

## 可复用分析接口

下述“只依赖 Mathlib”描述模块导入与证明依赖。整个 Lake 包仍固定 `goldbach-lean`，本轮不改变包的下载依赖。

- `Analysis.L2Fourier` 只依赖 Mathlib，提供经典 Fourier 与 L² Fourier 的一致性、
  L² 实数缩放、连续性、精确范数缩放和物理归一化。Hardy 内部限制与边界极限共同使用。
- `Analysis.SpectralData` 提供现有对角 Hilbert 空间数据的坐标与范数接口，供谱代数和
  迹证明共同使用，其导入不包含 Hardy 构造或算术证明。
- `Definitions.GeometryCore` 提供不带积分依赖的几何与尺度定义；
  `Definitions.BoundaryIntegral` 添加边界积分。旧 `Definitions.Geometry` 兼容导出两者。

导入策略检查这些边界，并编译实际使用分析接口的例子。旧 `Proofs.HardyFourier` 和
`Proofs.SpectralDataAlgebra` 入口保留。具体 Lean 用例见英文版文档。

其他项目可以直接导入这些接口。迁入上游仓库需要结合实际消费者及上游约定另行集成；
本轮保持已有依赖提交不变。
