from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1];status=json.loads((ROOT/'proof-status.json').read_text())
a=status['original_theorem_counts'];b=status['all_public_theorem_counts'];rows=status['declarations'];base=ROOT/'reference/Reviewed.lean'
complete = a['kernel_closed'] == 102 and not status['unusual_axioms']
closed=[r for r in rows if r['original'] and r['status']=='kernel_closed'];pending=[r for r in rows if r['original'] and r['status']=='proof_written_dependencies_pending']
p=['# Li–Liu Goldbach16：证明工程','',
'这是从已经逐项审阅的陈述稿开始的实际Lean证明工程。原文件作为不可变参考保存在`reference/Reviewed.lean`；原中文对照页面仍是审阅快照，不能用其`全部sorry`标识描述本工程的新进度。','',
'[查看当前证明进展及中文／Lean对照](progress.html) · [机器公理台账](proof-status.json) · [102条声明类型保真检查](reviewed-types.json)','',
f'基线的102个待证声明目前：**{a["kernel_closed"]}个已消除传递的sorryAx，{a["proof_written_dependencies_pending"]}个证明体已经写完但传递依赖仍未证明，{a["pending_direct_sorry"]}个仍是直接占位。** 另有新增辅助结果；计入全部公共lemma/theorem后，完全无sorryAx依赖的结果共{b["kernel_closed"]}个。辅助结果没有当作新增的论文命名定理。','',
'## 当前主结论的状态','',
('经原TeX逐项审阅的102条定理（正文及附录）全部通过Lean传递公理核验。常数与h的量词次序、GRH和S/R条件没有改变；171个原定义也保持不变。这里完成的是论文原有条件结论的形式化。' if complete else '1.1、1.2和素数对推论已经通过端到端的传递公理核验，常数与h的量词次序、GRH和S/R条件没有改变；其余原文条目的状态以下方台账为准。`Lean.collectAxioms`沿定义体和证明追踪传递依赖。'),'']
for name in ['theorem_1_1','theorem_1_2','primePair_consequence']:
 r=next(r for r in rows if r['name']=='LiLiuGoldbach16.'+name)
 p += [f'- `{name}`：{r["status"]}。本地待证依赖：'+(', '.join('`'+x.split('.')[-1]+'`' for x in r['pending_local_dependencies']) or '无')+'。']
p += ['', '## 已闭合的原审阅声明','']
for r in closed:p += [f'- [{r["name"].split(".")[-1]}]({r["file"]})（第{r["line"]}行）。']
p += ['', '## 已有证明体但还依赖未证对象／定理','']
for r in pending:p += [f'- [{r["name"].split(".")[-1]}]({r["file"]})：'+(', '.join('`'+x.split('.')[-1]+'`' for x in r['pending_local_dependencies']) or '无')+'。']
p += ['', '## 并行模块','',
'- `Proofs/Weights.lean`、`WeightNorm.lean`：光滑权、严格正质量、卷积与支集、范数积分和统一界。',
'- `Proofs/Characters.lean`、`KernelAlgebra.lean`：通用奇特征正交、完整Lemma3.1、有限Gram核与有限秩。',
'- `Proofs/SpectralAlgebra.lean`、`SpectralProducts.lean`、`SpectralDictionary.lean`：宽度代数、谱坐标与算子范数、复／四元数无穷乘积和零点，以及完整抽象谱字典。DictionaryApplication将其用于原文的Hardy算子。',
'- `Proofs/LFunctionDomain.lean`：导子GRH与Euler因子保证非本原奇特征的非零性、对数导数解析性及二维核可微性。',
'- `Proofs/Elementary.lean`、`Asymptotics.lean`：奇异级数的已有项目适配、eventual工具、log函数的可容许性和极限。',
'- `Proofs/PrimePowers.lean`、`PrimePairs.lean`：忠实于原相关和的坏素数幂质量、显式误差界、计数转换和最终条件推论。',
'- `Proofs/Main.lean`：原主定理的拼接。解析前置主链已经闭合；剩余的原陈述在`Remaining.lean`中列出。',
'- `BaseDefinitions.lean`与`Definitions.lean`：171个原定义保持原样。内线L²和边界迹存在性已给出真实证明；Hardy双向表示、闭迹子空间和精确范数均已闭合。','',
'- `Proofs/CharacterSeries.lean`、`CharacterAnalytic.lean`、`CharacterJoint.lean`：完整特征核级数、共轭对称和联合亚纯性。',
'- `Proofs/Hardy*.lean`：Fourier–Laplace正向表示、真实边界迹、全纯性和精确范数。',
'- `Proofs/Beta*.lean`：原Beta模型积分、绝对收敛、Gamma恒等式和竖线界。',
'- `Proofs/Mellin*.lean`、`Quadratic*.lean`：Mellin反演、原矩关系、泛函密度、Riesz表示和完整Prop7.4。',
'- `Proofs/SpectralCompletion*.lean`、`SpectralPositiveTrace.lean`、`SpectralHilbertSchmidt.lean`：完整谱乘积及对称性、基底无关性和正迹类基础。','',
'## 验证与复现','',
'```sh','lake build','python3 scripts/audit_proofs.py','python3 scripts/check_reviewed_types.py','python3 scripts/check_definitions.py','python3 scripts/write_progress_report.py','python3 scripts/build_progress.py','```','',
'在本目录运行。工具链固定为Lean4.35.0，Mathlib固定为`56a005855ea17e0b0958f73ec801ae140b0a1679`。Lake本地依赖`/home/azureuser/goldbach-lean`，复用其中`LiuSingularSeries`及已安装Mathlib；迁移到其他机器时须在lakefile.toml中调整该项目路径并保留锁定版本。既有两个Goldbach项目的源码未改动。','',
'`scripts/rebuild_remaining.py`会根据当前已经实际实现的原名字重建剩余占位索引。继续并行工作时，先让新模块独立编译，再运行该脚本并整体build，避免同名占位与证明并存。','',
'`reviewed-definitions.json`另外检查171个原定义的实际声明和函数体保持不变；只忽略空白及声明间注释，避免仅靠类型比较漏掉定义被改弱。HTML生成需要Pygments和KaTeX；本机自动复用已装依赖，其他机器可用requirements-review.txt和package.json安装。现成progress.html完全离线，不需要安装这些显示依赖。',
'`reviewed-types.json`来自Lean内的定义相等检查：把原快照命名空间的常量映射到当前命名空间后，逐一比较102条完整定理类型。它验证没有改动假设、结论与量词；不证明尚未完成的数学内容。','',
'`proof-status.json`中的公理清单由Lean内核环境的`collectAxioms`递归提取。允许的标准基础公理是propext、Classical.choice、Quot.sound；sorryAx单独视为未完成。目前未发现额外的非标准公理。类型保真测试所导入的旧占位只在验证脚本内使用，不由证明工程导入。','',
('## 完成情况' if complete else '## 后续主链'),'',
('正文及附录A/B的102条原审阅声明全部闭合。附录B.4单独证明了有限C6、宽支集且不对称权的Mellin模型公式，使用原交叉质量积分，而未套用窄支集对称权条件。完整构建、公理依赖、类型/定义保真、离线页面验证见verification.json。' if complete else '原审阅声明只剩附录B.4的最后宽权模型积分拼接；3.3、3.4、6.4、6.5、6.2与附录A已经闭合。全部未完成原文条目仍可在证明台账查阅。')]
(ROOT/'README.md').write_text('\n'.join(p)+'\n');print({'original':a,'public':b})
