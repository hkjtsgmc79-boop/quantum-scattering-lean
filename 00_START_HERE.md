# 一维量子散射框架 F2｜Lean 4.35.0 迁移交接

**本地 Lean 4.35.0 完整验证已通过。修复说明见 `FIX_REPORT.md`，原始证据见回传包。**

完整 F2 范围包括 23 个独立框架模块、40 个 Q5 模块和 2 个回归桥接及总验收模块。

## 1. 最简单的执行方式

把 ZIP 解压到一个**新的独立目录**，不要覆盖正在工作的4.30工程。用本地 Codex 或 VS Code 打开含 `lean-toolchain` 的整个目录，而非单个Lean文件。

在项目根目录运行：

```bash
bash scripts/complete_lean435.sh
```

该命令依次：

1. 检查本机 Python 3.9+、Git、elan；按项目锁定版本安装Lean 4.35.0，不改变elan全局默认值。
2. 解析并取得固定Mathlib及8个传递依赖，获取对应版本缓存。
3. 核对每个真实Git提交、工具链、依赖源码未修改，执行导入诊断。
4. 启动完整release验证：65个模块、示例、完整Lake入口、合并文件和55个重点声明的公理审计。

环境准备阶段可能需要联网下载。验证器在首个失败阶段停止并保存原始日志。

**依赖缓存不能跨Lean版本混用。**原4.30工程和缓存保留不动；新包在自身`.lake/`目录取得4.35依赖。不要用符号链接把它指回旧缓存。

## 2. 本机缺少 elan

验证工具不会自动下载执行一个未审阅的安装脚本。请采用Lean官方安装流程，或者让本地Codex按官方说明安装；不使用sudo、不卸载旧工具链、不改其他工程。

```text
https://docs.lean-lang.org/lean4/doc/quickstart.html
https://leanprover-community.github.io/install/project.html
```

环境准备单独运行：

```bash
bash scripts/prepare_lean435.sh
```

`PREFLIGHT_PASS`只表示环境及导入诊断通过，不代表本项目任何主定理通过。

## 3. 已有4.35精确版本环境：不下载，直接验证

可以直接运行：

```bash
bash scripts/verify.sh --target release
```

脚本默认寻找指定elan工具链与本项目Mathlib。也保留显式路径模式：

```bash
bash scripts/verify.sh --lean /absolute/path/to/lean \
  --mathlib-root /absolute/path/to/mathlib --target release
```

共享Mathlib只读：脚本不修改其源码、Git提交或缓存，不改其依赖。若提交或工具链不匹配，直接BLOCKED。

## 4. 固定版本

```text
Lean:   leanprover/lean4:v4.35.0
Mathlib tag: v4.35.0
Mathlib commit: 56a005855ea17e0b0958f73ec801ae140b0a1679
```

完整预期依赖在 `toolchain-lock.json`。它来自官方发布页和上游清单，是**预期锁定记录**；实际本机`lake update`生成的`lake-manifest.json`另行保存，不能用前者冒充后者。

## 5. 本地Codex操作

本次修复按原交接提示词 `01_LOCAL_CODEX_PROMPT.txt` 执行。重跑时以脚本生成的 `verification.json` 为准。

主入口保持：

```lean
QuantumScattering.reusable_scattering_framework_release
```

新增 `QuantumScatteringRelease.lean` 作为Lake默认目标，确保包含旧Q5依赖与桥接；原 `QuantumScattering.lean` 仍保持轻量核心入口。`lake build`成功不能代替示例、公理审计与合并文件的完整验证。

## 6. 回传一个文件即可

完整执行脚本每次使用新构建目录，结束后打印：

```text
reports/Quantum_Scattering_Lean435_return_<run_id>.zip
```

将最后一次实际运行的回传包交回主对话。它包含当前源码、真实原始日志、命令退出码、依赖清单、公理输出与哈希。环境准备阶段若在调用验证器之前失败，另带`reports/setup435_<run>/setup.log`和`exit_code.txt`。

只有`RELEASE_PASS`代表整条本地验证流程通过；`CORE_PASS`或`PREFLIGHT_PASS`都不是全项目完成。独立复现、物理语义审查和公开发表不由该状态自动证明。

## 7. 4.35新增的额外内核复核入口

本包提供 `scripts/check_kernel_linux435.sh`，供Linux环境在普通全工程通过后额外调用官方`lake check`或`lake check --paranoid`。该脚本需要 Linux。本次 macOS 验收使用普通 Lean 内核检查。
