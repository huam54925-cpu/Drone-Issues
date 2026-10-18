# UAV 通用弱对偶与闭合路线流量守恒：证明结果

验证日期：2026-10-18。本文记录本次实际执行的本地 Lean 检查。

本分支收录两个源文件：[WeakDuality.lean](../LeanCompletion/UAV/WeakDuality.lean) 和 [Flow.lean](../LeanCompletion/UAV/Flow.lean)。两者使用命名空间 `UAVProof`，均导入 `Mathlib`。

## 已证明的结果

### 通用有限维弱对偶

`WeakDuality.lean` 包含四个已完成的定理：

| 定理 | 结论 |
| --- | --- |
| `bounded_reduced_cost` | 若 `0 ≤ x ≤ u`，则 `u * min 0 q ≤ q * x`。 |
| `bounded_reduced_cost_sum` | 将上述不等式推广到有限指标集上的求和。 |
| `weak_duality_from_decomposition` | 从目标函数分解推导带变量上界修正的弱对偶下界。 |
| `finite_weak_duality` | 对有理数系数、有限指标集、变量界、等式约束和下界不等式约束，证明通用弱对偶不等式。 |

最后一个定理假设 `0 ≤ x(e) ≤ u(e)`、`Σ A(i,e)x(e) = b(i)`、`Σ C(k,e)x(e) ≥ 1`，以及割乘子 `z(k) ≤ 0`。令

```text
q(e) = c(e) - Σ_i y(i) A(i,e) + Σ_k z(k) C(k,e),
```

则证明

```text
Σ_i y(i)b(i) - Σ_k z(k) + Σ_e u(e) min(0, q(e)) ≤ Σ_e c(e)x(e).
```

这些是通用数学定理，不含 Case1 的具体数据或数值下界。

### 路线端点计数与流量守恒

`routeFlow route i j` 定义为相邻顶点对 `(i,j)` 在 `route.zip route.tail` 中出现的次数；重复经过同一条边按次数计数。`outFlow` 和 `inFlow` 分别对终点、起点求和。

| 定理 | 结论 |
| --- | --- |
| `outFlow_eq_source_count` | 在有限顶点类型上，出流等于路线边起点列表的出现次数。 |
| `inFlow_eq_target_count` | 在有限顶点类型上，入流等于路线边终点列表的出现次数。 |
| `route_endpoint_count_balance` | 边起点计数加路线末端计数，等于边终点计数加路线首端计数。 |
| `closed_route_flow_balance` | 若 `route.head? = route.getLast?`，则每个顶点的总出流等于总入流。 |

端点计数使用 `Option.toList.count`，因此空路线也有明确语义。归纳证明中的 `hsingle` 显式将单元素列表计数化为对应的 0/1 指示函数，再由 `omega` 使用归纳假设。闭合路线定理直接利用端点恒等式和首尾相等条件消去端点项，没有额外假设流量守恒。

这里的流量求和包括所有顶点（包括自环），尚未建立排除 `j = i` 的巡检次数等式。

## 实际验证与公理审计

| 检查 | 本次结果 |
| --- | --- |
| 对原始 `Flow.lean` 执行 `lake env lean LeanCompletion/UAV/Flow.lean` | 退出码 0，无警告。 |
| 在 `Flow.lean` 的完整源码副本后追加四个 `#print axioms` 并编译 | 退出码 0；已确认副本的源码前缀与此次上传的源文件一致。 |
| 在 `WeakDuality.lean` 的完整源码副本后追加四个 `#print axioms` 并编译 | 本次新执行，退出码 0，无警告。 |
| 两个文件的八个定理 | 没有 `sorryAx` 依赖；源码没有 `sorry` 或 `admit`。 |

`route_endpoint_count_balance` 的公理依赖为 `propext`、`Quot.sound`。其余七个定理的公理依赖均为 `propext`、`Classical.choice`、`Quot.sound`，没有额外自定义公理依赖。

检查在已有工程与缓存环境中完成，没有重新编译 Mathlib，也不是全新环境或 GitHub CI 验证。原始编译输出、审计副本与日志保留在本地源工程的忽略目录 `verification/runs/`，本分支只发布源码和这份整理后的结果说明。

## 验证环境与复现

- Lean：`leanprover/lean4:v4.30.0-rc2`，Windows x86_64；Lean 提交 `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`。
- Mathlib：`5450b53e5ddc75d46418fabb605edbf36bd0beb6`，已核对本地依赖的 HEAD。
- 原验证工程：[jsp-001022-lean-extension](https://github.com/huam54925-cpu/jsp-001022-lean-extension/tree/e04a61f1be1219c27f43c0bf3182794654b57f99)。其 `lean-toolchain`、`lakefile.toml`、`lake-manifest.json` 与该提交一致。两个 UAV 源文件来自工作区，以本分支收录的版本为准。
- 原工程的 Prim 依赖固定为 `a303f6bd23bb8f29a833d1d70327528359180995`；这两个源文件没有直接导入 Prim。

本分支没有另建 Lake 工程。复现时，使用上述固定版本的原验证工程并准备对应依赖与 Mathlib 编译缓存，将本分支的两个源文件复制到其 `LeanCompletion/UAV/` 目录，在该工程根目录执行：

```powershell
lake env lean LeanCompletion/UAV/WeakDuality.lean
if ($LASTEXITCODE -ne 0) { throw 'WeakDuality compilation failed' }
lake env lean LeanCompletion/UAV/Flow.lean
if ($LASTEXITCODE -ne 0) { throw 'Flow compilation failed' }
```

公理审计可在各文件的临时副本末尾追加对应定理的 `#print axioms UAVProof.<定理名>`，再执行 `lake env lean <副本路径>`。八个定理名已在上表完整列出；临时副本和输出应放在忽略目录中。

## 尚未完成的证明衔接

目前已经验证的是通用弱对偶定理，以及单条闭合路线到自然数边流的守恒性质。仍需将多机真实路线的访问次数、基地条件、连通性割、变量上界和目标函数系数逐项连接到弱对偶定理的前提。

本次没有运行 Case1 的 Python 精确证书验证器，也没有验证 `1158.3991045 km` 下界或四架机路线见证。因此，本次结果不能表述为“Case1 三机不可行已在 Lean 内核中完整证明”，也不代表已经完成全局最优性证明。
