# F2 主证明依赖地图

状态：下面的每条 Lean 链均为未编译候选。名称来自实际源码，不是待办清单。

## 1. 不依赖旧项目的核心

```text
F1 State/RealTransfer/LocalFlow/Layers/Channels/Scattering
              │                                  │
              ├── FlowComposition ── Refinement ─┤
              └── TransferComposition ──────────┘

F1 StackWave/LocalUniqueness/StackUniqueness/ExteriorModes
              └── Radiation ── FrameworkCompletion

F1 EvolutionInterface
              └── EvolutionUniqueness ── EvolutionSegment ── SmoothBackend
```

`RealEvolution.state_representation`：从任意实际解推出逆基本矩阵系数恒定和表示。
`EvolutionSegment.existsUnique_scattering`：变量实系数的有限段接上自由外部通道，实际解存在唯一。
`EvolutionSegment.complete_scattering`：真实 C¹/二阶方程/流及矩阵结果。
`SmoothBackend.smooth_physical_solution`：显式非恒定例子的物理方程和 C¹。

`ChannelTransfer.feedback_ne_zero` 与三条 cascade 结论：相干多次反射组合。
`Stack.split_scattering` 和 `Stack.split_tail_anywhere`：同介质精确细分保持 S 和实际状态。
`Problem.existsUnique_incoming_at_infinity`：只给无穷远的入射通道。
`Problem.current_arbitrary_classical`：不局限于标准散射构造的一般解恒流。

## 2. 真实旧项目桥接

```text
QuantumTunneling 40 modules (原 Q5 候选)
                    │
F2 Framework ── RectangularBridge
                    │
FrameworkCompletion ┴── ReleaseAcceptance
```

`RectangularBridge.wave_eq_legacy`：正确 sqrt(k) 输入缩放下全实轴函数相等。
`derivative_eq_legacy/current_eq_legacy`：实际导数、实际流相等。
`rawOutputs_eq_legacy/amplitudes_eq_legacy`：通过边界迹反推出射振幅，而不只比概率。
`scatteringMatrix_eq_legacy`：完整复矩阵相等。
`framework_complete_resonance`：旧共振分类在新单层实例上的结论。
`framework_physical_families`：连接旧的透射率与复 S 能量参数函数，供原极限/连续性定理复用。

最终入口：`QuantumScattering.reusable_scattering_framework_release`。
`FrameworkReleaseCertificate` 的字段都是输出结论；不是用户必须先提供的假设。

## 3. 后期局部修复顺序

先修复23个纯核心模块，再修复旧Q5依赖，最后编译桥接和ReleaseAcceptance。
只凭 core 通过不能报告全项目通过。变量后端实现中 derivative_a/b/c/d、复数投影/标量转换、
零导数⇒常值的区间API、Filter 极限与期望最终类型是最可能需要编译反馈的地方。
这些是接口风险提示，不是已取得的 Lean 报错清单。
