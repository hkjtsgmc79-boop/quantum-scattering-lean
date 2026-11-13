# Lean 4.35.0迁移：已查阅的官方来源

查阅日期：2026-11-13。以下为本轮通过网页实际读取的来源，不是本机Git克隆或编译记录。

1. Lean正式4.35.0发布页：
   https://github.com/leanprover/lean4/releases/tag/v4.35.0
2. Mathlib v4.35.0发布页及其完整提交：
   https://github.com/leanprover-community/mathlib4/releases/tag/v4.35.0
   https://github.com/leanprover-community/mathlib4/commit/56a005855ea17e0b0958f73ec801ae140b0a1679
3. 同提交的工具链文件：
   https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/lean-toolchain
   返回 leanprover/lean4:v4.35.0。
4. Mathlib发布标签中的依赖清单：
   https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.35.0/lake-manifest.json
   8个传递依赖的完整预期提交已逐项记录在toolchain-lock.json。
5. Lean 4.35.0官方迁移说明：
   https://lean-lang.org/doc/reference/latest/releases/v4.35.0/
   涉及rwa行为、实例推断及新增Lake内核检查工具；源码扫描没有发现本项目使用rwa、Lean.reduceBool或Lean.trustCompiler。未自动启用向后兼容选项、未绕过内核检查。
6. Mathlib项目更新与缓存说明：
   https://leanprover-community.github.io/install/project.html

部分固定版本Mathlib API原始页面在网页抓取中返回cache miss，因此没有声称逐个数学API都已核对。Compatibility435.lean在有实际环境时检查本项目导入路径及基本导数接口；它仍不等于整个证明工程的编译验证。

原F2/Q5数学来源和旧工具链记录保存在history/lean430_baseline/，不删除、不改写为本轮成果。
