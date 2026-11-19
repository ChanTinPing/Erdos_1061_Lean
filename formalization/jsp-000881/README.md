# JSP-000881 · Erdős #1061

目标是证明不存在正实数 $c$ 使原题的有序解计数 $S(x) \sim cx$。计数采用 [Formal Conjectures 的题目陈述](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1061.lean)。

[无条件定理 `Jsp000881.not_linear_asymptotic`](compat/UpstreamJspReduction.lean) 在 Lean v4.34.1 中使用固定的上游依赖，并接上两个实际的 Vaughan 降秩分支。公理检查只列出 `propext`、`Classical.choice` 和 `Quot.sound`。完整编译方法见 [上游兼容入口](../prime-uniformity/compat/README.md#同一工具链中的原题入口)。

| 文件 | 内容 |
| --- | --- |
| `Plane.lean` | Li 的整数参数平面、固定格点参数化、两条方程、平面交点和方向行列式 |
| `Solutions.lean` | 把按大小排序的六素数元组注入有序解，验证约数和等式 |
| `Reduction.lean` | 对接原题计数，由不同六元组的超线性下界推出否定答案 |
| `Counting.lean` | 有限集去重与平面交点损失上界 |
| `Heights.lean`、`Rectangles.lean` | 显式格点矩形、六坐标的正性和排序、周长上界与实际素数点计数 |
| `Scaled.lean` | 固定尺度 $z=k^7, T=2^k$，从参数筛和六仿射式素数点下界推出原题的否定答案 |
| `Local.lean`、`SieveBounds.lean`、`ParameterSieve.lean` | 识别退化的三种同余条件，证明局部可容许的参数保留正比例 |
| `PrimeWeights.lean` | 从六个素数支持 von Mangoldt 权重的相关和下界推出最后结论 |
| `Coefficients.lean`、`Products.lean` | 六式的对数幂系数界和截断奇异乘积的统一正下界 |
| `ResidueRectangles.lean`、`CRTIntersection.lean` | 矩形上固定剩余类的点数误差及二维 CRT 局部条件合并 |
| `Bonferroni.lean` | 截断包含排斥的奇数下界和偶数上界，适用于非负权重 |
| `LatticeArea.lean`、`CramerSieve.lean`、`CramerBudget.lean`、`CramerMass.lean` | 精确边长、任意整数矩形的截断筛及有限 Cramér 主项 |
| `CramerHarmonic.lean`、`CramerDecay.lean` | 二进制调和和与截断误差极限，证明允许的截断尺度下 Cramér 主项统一为正 |
| `CramerPrimeBlocks.lean`、`CramerNormalization.lean` | 用中央二项式系数控制二进制素数块，得到 Cramér 权重的对数幂上界 |
| `GowersStep.lean`、`GowersIteration.lean`、`GowersFourier.lean` | 五轮有限域方向 Cauchy–Schwarz、有限 Fourier 反演和两个区间权在转移中的损失 |
| `ModularDirections.lean` | 实际六式化为有限域仿射式，验证十五对方向独立性所需的模数界 |
| `TriangleCutoff.lean`、`TriangleInterval.lean` | 以 Fourier ℓ¹ 范数为 1 的三角形区间权控制矩形相关和 |
| `AmbientPrime.lean`、`PrimeCharacter.lean`、`PrimeTriangle.lean` | 选择素数模数、构造加法特征及三角形权转移 |
| `ModelTransfer.lean` | 展开六次单因子替换，从模型主项及替换误差推出所需加权估计 |
| `PrimeInput.lean` | 导入独立素数一致性包，并指定固定阶 5 与指数 1280 |
| `RectangleRadius.lean`、`PrimeCutoffGrowth.lean`、`RectangleWeightBound.lean`、`RectangleErrorDecay.lean` | 实际尺度、解析截止值、五个伴随权重和最终误差极限 |
| `RectangleMask.lean`、`RectangleField.lean`、`MaskedTransfer.lean`、`MaskedModel.lean` | 中央子矩形、精确模素数求和、加权模型主项及转移 |
| `AffineTransfer.lean`、`RectangleCorrelation.lean`、`PrimeReduction.lean` | 六个具体仿射式的替换误差及原题的完整条件归约 |
| `InverseReduction.lean` | 从五阶区间逆定理、素数在算术级数上的估计及四步幂零测试降阶推出原命题 |
| [prime-estimate.md](prime-estimate.md) | 六线性式素数计数的现成定理、所需特例和形式化路线 |

两个包已用固定版 Lean v4.33.0 联合构建。入口 `not_linear_asymptotic_of_prime_uniformity` 将原命题归约到 `QuantitativePrimeGowersUniformity`，即一维真实素数权重和 Cramér 权重之差满足固定的 $U^5$ 矩估计 $\|\cdot\|_{U^5}^{32}\ll(\log X)^{-1280}$。Cramér 主项、模素数转移、六次替换、平面筛和原题计数均已接通。`not_linear_asymptotic_of_inverse_and_step_descent` 将这个归约接到五阶逆定理、算术级数素数估计及幂零测试降阶。

整数参数平面对应 Li 证明里分母 $q=1$ 的子族。该子族的解数下界足以推出完整 Erdős #1061 的否定结论。

[v4.34.1 兼容入口](compat/UpstreamJspReduction.lean) 已在同一 Lean 环境中接通两条上游分析定理和本包计数，并验证了竖直 Fourier 选取和零频率降阶。`not_linear_asymptotic_of_native_vertical_step_descent` 的唯一前提是非零竖直频率的定量降阶 `NativePrimeVerticalStepDescent 4`。编译与验证记录见 [上游兼容入口](../prime-uniformity/compat/README.md)。

同一入口也已通过公理检查验证 `not_linear_asymptotic_of_native_rank_step_descent`。它从 `NativePrimeRankStepDescent 4` 推出原命题。这个接口只要求在每次大相关中降低一秩或直接降低一步，由已经验证的迭代统一吸收各次复杂度和相关性损失。

## 包依赖

本包通过 Lake 直接导入 [PrimeUniformity](../prime-uniformity/README.md)。两个包各自固定工具链和依赖。当前分支采用相邻目录的路径依赖，发布到两个仓库时可将该条依赖改为固定 Git 提交。

## 编译

从仓库根目录进入此目录。工具链与 Mathlib 都固定在 `v4.33.0`。

```sh
cd formalization/jsp-000881
mapfile -t needed < <(awk '
  $1 == "import" && $2 ~ /^Mathlib[.]/ { print $2 }
  $1 == "public" && $2 == "import" && $3 ~ /^Mathlib[.]/ { print $3 }
' Jsp000881/*.lean ../prime-uniformity/PrimeUniformity/*.lean | sort -u)
lake exe cache get "${needed[@]}"
LEAN_NUM_THREADS=1 LEAN_STACK_SIZE_KB=32768 lake build
```

编译后可在临时 Lean 文件中核对最后归约的类型及公理。

```lean
module

import Jsp000881

#check Jsp000881.not_linear_asymptotic_of_prime_uniformity
#print axioms Jsp000881.not_linear_asymptotic_of_prime_uniformity
#print axioms Jsp000881.not_linear_asymptotic_of_inverse_and_step_descent
```

`not_linear_asymptotic_of_native_prepared_rank_step_descent` 已在 v4.34.1 与固定上游依赖同环境检查。它把原命题归约到 `NativePrimePreparedRankStepDescent 4`。余下的单步定理作用于已经归一化、选好适配基、且顶秩频率非零的原生测试，并给出实际 Vaughan Type I 或 Type II 分支。
