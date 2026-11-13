# F2 的 Lean 4.35.0 本地修复记录

2026 年 11 月 13 日。使用 Lean 4.35.0（`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`）和 Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`。Lake 实际生成的依赖清单与锁定的 Mathlib 及八个传递依赖一致。

## 验收证据

运行编号 `20261113T125659785426Z`。一键入口返回 `RELEASE_PASS`，退出码为 0。默认 `lake build` 也已通过。39 项工具测试全部通过。三份日志分别保存在回传包的 `verification/complete.log`、`verification/lake-build.log` 和 `verification/tooling-tests.log`。

完整验证器在全新的构建目录编译 65 个模块、三个示例套件、两个合并文件及项目入口。55 项重点声明的允许公理为 `propext`、`Classical.choice`、`Quot.sound`。核心合并文件重复审计 45 项，完整合并文件重复审计 55 项。原始输出、公理明细、编译退出码、编译产物哈希和构建前后的源码哈希见回传包中的 `verification/`。

原交接包与原始校验记录保留在本机，基线文件 `migration-baseline.json` 和 `inherited-sources.json` 保持原样。`contracts.json` 及其保护的 14 段文本逐字节一致。修复涉及 65 个数学模块中的 44 个。公开证明陈述保留原有假设和结论，`rightFlow_slope_deriv` 明确先在实数上平方再嵌入复数，`ℂ × ℂ` 补上解析所需空格。

## 数学源码

| 文件 | 修复 |
| --- | --- |
| `QuantumScattering/State.lean`、`QuantumTunneling/CoherentCurrent.lean` | 通过实部和虚部的连续线性映射应用链式法则，证明实际概率流的导数为零。 |
| `QuantumScattering/LocalFlow.lean`、`Layers.lean`、`QuantumTunneling/PropagationProfile.lean` | 显式处理奇函数除法、逐点函数运算与层系数投影，维持振荡、临界和衰减三种传播。 |
| `QuantumScattering/Channels.lean`、`Scattering.lean`、`TransferComposition.lean`、`QuantumTunneling/ScatteringMatrix.lean` | 规范复共轭和分母的表达，应用非零证明，逐项证明矩阵幺正、相位抵消与相干组合。 |
| `QuantumScattering/StackWave.lean`、`FiniteScattering.lean`、`PhysicalModel.lean`、`ExteriorModes.lean` | 显式证明拼接状态的分量等于对应分段函数，修复平移导数、归一化、概率流及外部平面波中的类型转换。 |
| `QuantumScattering/LocalUniqueness.lean`、`StackUniqueness.lean`、`FlowComposition.lean`、`Refinement.lean` | 展开平移复合与端点条件，明确有限层传递的解码，以及精确细分所需的分段分支。 |
| `QuantumScattering/EvolutionInterface.lean`、`EvolutionUniqueness.lean`、`EvolutionSegment.lean`、`SmoothBackend.lean` | 修复 Wronskian 和逆基本矩阵系数的导数计算、变量系数段的拼接与边界迹，以及显式非恒定势的物理方程。 |
| `QuantumTunneling/PlaneWave.lean`、`BarrierWave.lean`、`Normalization.lean`、`C1Regularity.lean`、`TransferWaves.lean`、`TransferNormalization.lean`、`ScatteringUniqueness.lean` | 分开证明函数相等与导数系数相等，展开平移和非零幅度归一化，保留实际导数和全局 C¹。 |
| `QuantumTunneling/TransferAmplitudes.lean`、`RectangularModel.lean`、`PhysicalResonance.lean`、`AllEnergyStatement.lean` | 明确幅度平方与倒数的改写、物理波函数投影以及透射和反射概率的实际流比。 |
| `QuantumTunneling/IntervalRigidity.lean`、`FundamentalRepresentation.lean`、`TwoSidedStates.lean`、`GeneralScatteringUniqueness.lean`、`RadiationAtInfinity.lean` | 修复闭区间端点条件、逆矩阵表示、镜像波、两端迹和自由区相位代数，保留任意函数的唯一性。 |
| `QuantumTunneling/RegularizedTransmission.lean`、`ThresholdContinuity.lean`、`ResonanceClassification.lean`、`PhysicalLimits.lean`、`ScatteringContinuity.lean` | 显式构造滤子极限和分母正性，修复阈值连续性、共振指标、厚势垒渐近系数及复矩阵连续性。 |
| `QuantumTunneling/BidirectionalProject.lean` | 移除误粘贴在证书构造体内的三条重复字段声明。结构类型及三个字段的实际证明均保留。 |
| `QuantumScattering/RectangularBridge.lean` | 证明两边波数及各区间 ODE 系数相同，显式约去非零的 `sqrt(k)`，保留波函数、导数、流、复幅度和完整复矩阵的严格等价。 |

## 构建与复现

- `State.lean`、`Compatibility435.lean`、`scripts/build_support.py` 改用实际所需的 Mathlib 导入，合并文件从源模块收集导入并重新生成。
- `scripts/prepare_lean435.sh` 使用本机 elan 支持的查找方式，在下载缓存前核对 Lake 解析出的依赖，并补建 Mathlib 缓存命令未生成的 Cli 库。`scripts/verify.py` 把 Q5 顶层入口和实际 Lake 清单纳入验证。
- 两项原来要求源码与迁移前候选逐字节相等的工具测试，现分别检查历史基线记录一致性和交付源码哈希。契约、公理名单及审计声明清单保留。
- 本次先使用已锁定的本机 4.35.0 缓存定位错误，随后把该依赖复制到 F2 自己的 `.lake/packages`，由 Lake 生成本项目依赖清单并执行默认构建。
- 本机验收使用普通 Lean 内核检查。跨机器独立复现、Linux 附加内核复核及独立物理语义审阅尚未执行。
