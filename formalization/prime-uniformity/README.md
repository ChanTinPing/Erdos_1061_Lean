# 定量素数 Gowers 一致性

这是一个独立 Lean 包，目标是证明真实素数权重与 Cramér 模型之差，在每个固定阶的 Gowers 范数下具有任意对数幂节省。纸面输入取自 Green–Sawhney [命题 4.4](https://arxiv.org/abs/2410.04189)，该命题使用 Leng 和 Tao–Teräväinen 的定量结果。

`PrimeUniformity.GowersUniformityEstimate d A` 陈述固定阶 $d$、固定指数 $A$ 的估计。权重差在 $[1,X]$ 上取值，零延拓到素数域 $\mathbb F_p$，其中 $4(d+3)X<p\le8(d+3)X$。所用的归一化立方体矩是 $U^d$ 范数的 $2^d$ 次方，所需上界为 $C(\log X)^{-A}$，常数 $C$ 统一于充分大的 $X$ 和该范围内的素数 $p$。总命题 `PrimeUniformity.QuantitativePrimeGowersUniformity` 量化每个固定 $d\ge2$ 和每个自然数指数 $A$。

| 模块 | 内容 |
| --- | --- |
| `Weights.lean` | 只支持在素数上的 von Mangoldt 权重、有限 Cramér 权重及零延拓 |
| `Gowers.lean` | 归一化有限平均、差分与任意阶立方体矩 |
| `CubeLift.lean` | 区间支撑内立方体关系的模素数无绕回提升 |
| `CubeProduct.lean` | 递归 Gowers 矩等于显式立方体乘积的平均 |
| `IntervalMoment.lean` | 整数区间立方体和与循环群矩的精确等式、单位权重归一化、区间估计推出循环群估计 |
| `GowersProducts.lean` | 有限交换群上的张量积，以及中国剩余分解下的立方体矩乘法 |
| `GowersSum.lean` | 立方体矩非负性和只损失阶数常数的加法上界 |
| `IntervalNorm.lean` | 支撑内立方体平均、取根及将权重缩放到 1 有界 |
| `IntervalBounds.lean` | 区间加法上界与中间模型的两段误差合并 |
| `LogSavings.lean` | 伸展指数误差转成任意对数幂节省，并把定量多项式损失吸收到正幂尺度中 |
| `SiegelModel.lean` | Siegel 权重及用论文中的误差形式推出总估计 |
| `IntervalSupport.lean` | 稀疏支撑的立方体上界与区间立方体数下界 |
| `PrimePowers.lean` | 从普通 von Mangoldt 转为只在素数上取值，保持任意对数幂节省 |
| `CramerNormalization.lean` | 复用 JSP 的 Cramér 权重多对数上界 |
| `StrictCutoffTransfer.lean` | 论文严格截断与原题闭截断的端点误差 |
| `AffinePolynomial.lean` | 逆仿射代入清分母，并保留每个系数的逼近尺度 |
| `PhaseDetection.lean` | 从稠密的近整数点提取一个有显式频率上界的大指数和 |
| `PolynomialRecurrence.lean` | 分隔节点插值，把单项式粗逼近收紧为与近整数容差成比例的误差 |
| `WeylInverse.lean` | 给普通多项式的最高次系数构造显式的小分母，在平移区间上实例化单变量相位逆定理 |
| `DilationRecurrence.lean` | 从单变量逆定理恢复分离形系数，并合并有限族的分母 |
| `DyadicDilation.lean` | Type II 的双变量回收和 Type I 的单变量回收，含短区间分支 |
| `DilationDescent.lean`、`DilationDescentLabels.lean` | 冻结稠密伸缩参数族中的同一有理约束组，清除仿射采样分母，同时恢复所有约束行和正次数的原尺度系数 |
| `DilationDescentSplit.lean`、`NilsequenceKernel.lean` | 将水平系数拆入公共核、平滑项和有理项，控制平滑增量和有理坐标周期，证明坐标公共核继承成对核的降阶 |
| `NilsequenceFreezing.lean` | 用平滑因子的统一近似界控制相关性误差，并在一个短区间与剩余类的交集上保留相关性 |
| `Bilinear.lean` | Type II 双线性和的两次 Cauchy–Schwarz、乘积截断与稠密相关点对 |
| `TypeI.lean` | 从加权和提取较大相关的因子、精确区间切片及对数权重前缀展开 |
| `TypeIProgressions.lean` | 用精确步长 $q/\gcd(q,d)$ 重排 Type I 前缀，保持稠密伸缩参数、相关性和仿射采样区间的长度界 |
| `TypeIDilationBudget.lean` | 在短二进区间直接清除单点的分母，在长区间使用 Weyl 回收，两种情形都有统一的公共分母和误差界 |
| `TypeIVaughanScale.lean` | 统一控制 Type I 伸缩族的密度、投影行和系数回收所需的余因子尺度 |
| `TypeIIDilationBudget.lean`、`TypeIIVaughanScale.lean` | 用 Vaughan 块的实际长度控制 Type II 的 Weyl 回收，统一估计未伸缩系数的公共分母与误差 |
| `TypeIIProgressions.lean` | 在 Vaughan 列相关中选择共用剩余类，去掉乘积上的级数掩码，得到有显式长度下界的伸缩区间 |
| `Vaughan.lean` | Vaughan 的精确卷积恒等式及 Type I/II 系数的支撑和大小 |
| `ProgressionBoundary.lean` | Cramér 算术级数筛，以及从素数定理推出全模数、全剩余类比较 |
| `CramerTypeI.lean` | Cramér 的 Möbius 除数展开、Type I 截断和伸展指数总误差 |
| `PrimeCorrelation.lean` | 在区间子集上精确展开素数与 Cramér 的相关和，将 Vaughan 的对数权移到无权前缀，并控制截断造成的加权误差 |
| `PrimeCorrelationBounds.lean`、`TypeIIBlocks.lean` | 用共同的 Type I 前缀预算控制素数相关和，精确分解 Vaughan Type II 的二进块并提取稠密列相关 |
| `TypeIPrefixes.lean` | 从大的素数–Cramér 相关性提取稠密 Type I 伸缩参数或一个相关性大的 Type II 块 |
| `PrimeCorrelationScale.lean` | 消去 Vaughan 低截止与 Cramér 截断误差，从带级数掩码的区间相关性获得显式指数阈值 |
| `PrimeProgressionTests.lean`、`CorrelationDescent.lean` | 用算术级数比较控制零步测试，验证有限次降阶的参数损失足以达到所需素数正交性 |
| `UpstreamInverseReduction.lean` | 对同一批测试应用区间逆定理和素数正交性，从严格 Cramér 截断推出目标 Gowers 估计 |
| `Estimate.lean` | 固定阶与任意固定阶的定量素数估计目标 |

定义、整数提升及区间归一化转换都已经过 Lean 检查。按原论文路线，分析输入包括普通 von Mangoldt 与 Siegel 模型的伸展指数估计、Siegel 修正项的例外模数幂节省，以及例外零点的距离界。下面也记录使用上游零点间隔定理省去修正项的路线。JSP-000881 只使用 `GowersUniformityEstimate 5 1280`。

## 论文中的证明依赖

Green–Sawhney 命题 4.4 先用 [Leng，第 5 节定理 7](https://arxiv.org/abs/2312.10772) 控制真实素数与 Siegel 模型，再用 [Tao–Teräväinen，定理 2.5](https://doi.org/10.4171/jems/1404) 控制 Siegel 模型与 Cramér 模型。Siegel 定理把后一项对例外模数的幂次节省转成任意对数幂节省。最后用 Gowers 范数的三角不等式合并两项，并从整数区间转为本包的有限域归一化。`gowersUniformityEstimate_of_siegel_bounds` 已核验从这三个分析输入到循环群目标的归约。它处理没有例外零点的分支，以及 Cramér 截断取整对对数大小的影响。`gowersUniformityEstimate_of_vonMangoldt_siegel` 直接接收 Leng 对普通 von Mangoldt 权重的估计。它结合已经形式化的真素数幂误差，因此上游无需另证只支持在素数上的版本。

### 排除例外零点的路线

OpenAI 的 [`exists_absolute_real_zero_gap`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/NumberTheory/SiegelZeros/Conclusions/Theorem.lean) 给出实零点的统一下界 $c\le (1-\beta)\log q$，已有独立 [Comparator 复核](https://hexagonmath.org/2611.00200v2)。Tao–Teräväinen 定义 2.1 允许选取足够小的绝对常数 $c_0$。取 $c_0\le c$ 后，$q\le Q$ 和 $1-\beta<c_0/\log Q$ 不能同时成立。当前 Lean 已证明这个比较 `not_exceptional_of_uniform_log_gap`，并给出无修正情况下的归约 `gowersUniformityEstimate_of_vonMangoldt_cramer`。现有工具链固定在 v4.33.0，上游固定在 v4.34.1，尚未引入依赖。严格截断 $p<Q$ 和闭截断 $p\le\lfloor Q\rfloor$ 的差已经在 Lean 中证明保留任意对数节省。

没有例外零点时，Leng 的素数侧证明可以省去扭曲 Type I 和例外修正，仍需要高阶逆定理，以及普通 Type I/II 的幂零序列相关估计。其归纳末步所需的普通算术级数素数定理，在上游有候选 [`residuePsi_exponential`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/NumberTheory/Jacobsthal/Sieve/LargeModulusSiegelWalfisz.lean#L512)，给出到 $\exp((\log X)^{1/3})$ 的模数范围和伸展指数误差。本包已经证明这个量级的素数定理足以给 Leng 所需的全部算术级数比较，包括任意子区间、非既约剩余类和大模数。`UniformPrimePrefixEstimate.of_real_range` 接收上游使用的实数高度、取整和从零开始的前缀定义。Cramér 一侧的伸展指数误差通过 CRT、Bonferroni 和明确的阶乘尾项在本包内证明。目前上游定理还未作为本分支的实际 Lean 依赖。

### 上游逆定理和剩余相关估计

上游 [`exists_native_integer_interval_inverse`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/Progressions/Lattices/NativeIntegerIntervalInverse.lean) 适用于所有固定阶。在整数区间上，1 有界函数的 $U^{s+1}$ 范数至少为 $e^{-p}$ 时，它给出次数 $s$ 的 native 幂零测试，相关性至少为 $e^{-(p+C)^C}$。上游使用支撑内立方体数归一化。本包的 `normalizedIntervalCubeSum_eq_supportedCubeAverage` 和 `intervalGowersNorm_mul_const` 已核验这一数学归一化及权重缩放。两个包的 Lean 声明尚未在同一工具链中互引。

同一上游提交也有 [同时幂零测试分解](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/Progressions/Nilpotent/SimultaneousNiltestFactorization.lean) 和 [固定剩余类冻结](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/Progressions/Lattices/FixedAffineResidueDescent.lean) 的定量证明。仍需证明 Leng 命题 5.4 中使用附录 A.10–A.12 的伸缩参数回收步骤，从 Type II 产生的许多 $g(dn),g(d'n)$ 成对相关，推出原数列可用于降阶的统一定量结构。附录 A.12 需要的逆仿射分母清除已在 `AffinePolynomial.lean` 证明，上游 [`realAxisAffinePullback_coeff_bound`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/Progressions/Lattices/FullAffineCoefficientBound.lean) 提供实系数误差界。A.11 在命题 5.4 中用于分离形相位 $\alpha\ell^k+\beta\ell'^k$。本包的 `recover_separable_dilation_from_phase_inverse` 已将该标量步骤归约为单变量普通相位逆定理 `MonomialPhaseInverse`。密度为 $\rho$ 的近整数点先给出 $0<m<R$ 的大指数和，阈值为 $\rho/16$，其中 $16\le\rho R$。逆定理给出分母至多 $D$ 的粗逼近后，插值回到原近整数点，恢复随容差线性缩小的误差。两条纤维的共同分母至多 $(RD)^2$。定理列出容差和点数所需的不等式。`recover_pair_dilation_at_ambient_scale` 从点数选择插值节点间距，并把 $N/L$ 尺度上的成对系数误差恢复到原多项式的 $N^{-k}$ 尺度。

求粗逼近使用定量 Weyl 逆定理。对次数 $k>0$ 的多项式，若平均相位至少为 $1/n$，`WeylInverse.leading_inverse` 给出显式的分母和归一化误差上界 `leadingInverseBudget k n`。`leadingInverseBudget_polynomial` 证明固定次数时该上界是 $n$ 的多项式。`monomialPhaseInverse_Ico` 用整数平移保留最高次系数，将这个结果接上 `MonomialPhaseInverse`。这些文件从上游 [`WeylInverse01.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/SumProduct/Alignment/WeylInverse01.lean) 的标量证明提取并显式化了参数，在本包的 Lean v4.33.0 工具链可编译。

在 Type II 的区间 $[L/2,L]$，`recover_pair_dilation_dyadic` 直接给出原尺度上的系数误差和分母。`common_denominator_of_coefficient_estimates` 把有限个次数和约束行的分母合在一起。固定次数下，二进区间引理的尺度门槛对密度的倒数和输入误差预算是多项式。在命题 5.4 的范围，$L$ 和 $N/L$ 都至少为 $N^{1/3}$，因此 `eventually_natPolynomial_eval_le_rpow` 可用于吸收固定次数的多项式预算。Type I 没有 $L\ge N^{1/3}$ 的下界。若点数不足以插值，`recover_single_dilation_dyadic` 从一个符合条件的 $\ell$ 取分母 $\ell^k$，仍给出原尺度上的误差界。

两次 Cauchy–Schwarz 之后，从平方相关下界提取具有较大相关性的稠密点对，已由 `dense_large_column_correlations` 核验。固定一个剩余类后，`typeII_column_correlation_residue` 将两个乘积截断化为伸缩参数的一段整数区间。`exists_common_large_residue_subsums` 给出在许多相关和中固定同一剩余类时的损失。进一步的上游候选 [`exists_native_pair_vertical_step_drop`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/Progressions/Estimates/TranslationMajorTwistedCorrelationStepDrop.lean#L225) 给出受控的乘积符号分解。从中获得固定系数约束的路线是投影到相应次数的水平商，在稠密点对中固定有界高度的子空间及有理网格，再使用已经证明的标量回收。随后通过水平位置重建并投影到更低的次数或秩。可将一对测试嵌到四个槽位，另外两个槽位取常值 1，从而直接使用上游的 `projectedHorizontal_factorization` 与 `layerHorizontalImage_frequency`。对每个次数在秩二层取商，使用 `realHorizontalSymbolHom` 的可加性抽出系数约束。回收后用 `exists_polynomialOrbit_factorization_rank_two` 做单轨道重分解，再通过 `horizontalTreeValue_mk` 和 `exists_controlled_lower_rank_quotient` 降低秩。秩为一时可以下降整个次数。这部分还需 Lean 接线并证明整个素数相关估计的迭代。

专项复核使用上游提交 `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` 的 `lean/` 和其锁定依赖。每次单独构建一个所用模块并检查对应声明的公理。

```lean
module

import OAI.Combinatorics.Progressions.Lattices.NativeIntegerIntervalInverse

#print axioms OAI.Erdos3.exists_native_integer_interval_inverse
```

```lean
module

import OAI.NumberTheory.Jacobsthal.Sieve.LargeModulusSiegelWalfisz

#print axioms OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.residuePsi_exponential
```

```lean
module

import OAI.NumberTheory.SiegelZeros.Conclusions.Theorem

#print axioms OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap
```

公开复核覆盖了逆定理所在的模块，专项公理审计仍需核对声明本身。上游工具链是 Lean v4.34.1，本分支固定 v4.33.0。已在 v4.34.1 串行复核各算术接口的前 14 个依赖模块。上游首个需要全量 `import Mathlib` 的原样依赖触发了 1730 MiB 的进程限制。将上限提高到 1840 MiB 后，独立的全量导入也触发了停止线。完整的上游声明及与本包互引仍需在可用内存更大的环境复核。 [独立双内核复核记录](https://github.com/carlostoledo1891/cert-machine/blob/9814e4c06281e34a113ce853d7d99ccce160b750/certs/openai-math-kernel.json)

## 水平系数回收后的缺口

`recover_frozen_pair_dilation` 和 `recover_frozen_single_dilation` 已把稠密伸缩证书转成原尺度上的共同分母逼近。`exists_horizontal_positive_degree_split` 接收每个次数的整数约束矩阵和清除分母的右逆，在系数层得到公共核、平滑多项式和有理多项式。平滑项具有显式的大小和增量界，有理坐标在共同整数模数下周期。`coordinateAnnihilator_lowerCentralSeries_eq_bot` 证明单轨道的公共核继承成对核的低阶。

仍须从上游 `ControlledSymbolFactorization` 抽出统一的有界约束矩阵和右逆，把系数层分解提升到原幂零轨道的各层，并验证有理轨道在格陪集上的周期性。`exists_large_frozen_progression_piece` 将平滑因子的近似界转为一段短算术级数上的相关性下界。该引理仍需与具备复杂度控制的低阶轨道和观测函数连接。

非零竖直频率的阻塞点在成对符号到单轨道的恢复。上游 `exists_native_pair_affine_cell_step_drop` 的结论是成对符号的 BCH 因子分解。现有标量伸缩定理使用加性系数，因此须先用 `projectedHorizontal_factorization` 提取水平商中的加性式，再用 `layerHorizontalImage_frequency` 把恢复出的约束接回竖直频率。若采用上游的 `exists_controlled_lower_rank_quotient`，须在固定次数内追踪秩。秩下降本身保持次数，秩归零才可用 `Niltest.dropTop` 获得下一次降阶所需的测试。

`eventually_prime_cramer_orthogonal_of_descent` 已接通零步的算术级数估计，并吸收每次降阶的幂次预算。每次降阶允许对数预算从 $\max(2,\log\log X)$ 起步，以容纳有限分解中的对数损失。[v4.34.1 兼容入口](compat/README.md) 已实际导入上游区间逆定理和算术级数素数定理，并为原生测试族验证 `IntervalCorrelationInverse`、复杂度单调性和零步条件。还须证明该测试族的 `PrimeCramerStepDescent 4 nativePrimeTests`。

## 编译

在本包根目录使用固定的 Lean 和 Mathlib `v4.33.0`。

```sh
mapfile -t needed < <(awk '
  $1 == "import" && $2 ~ /^Mathlib[.]/ { print $2 }
  $1 == "public" && $2 == "import" && $3 ~ /^Mathlib[.]/ { print $3 }
' PrimeUniformity/*.lean | sort -u)
lake exe cache get "${needed[@]}"
LEAN_NUM_THREADS=1 LEAN_STACK_SIZE_KB=32768 lake build
```
