# JSP-000881 的六仿射式素数计数

## 已核验的最终归约

`PrimeReduction.lean` 中的 `not_linear_asymptotic_of_prime_uniformity` 只接受独立包 [PrimeUniformity](../prime-uniformity/README.md) 的 `GowersUniformityEstimate 5 1280`。给定长度 $X$，取 $Q=\lfloor\exp((\log X)^{1/10})\rfloor$。令 $f$ 为 $\Lambda'-\Lambda_{\mathrm{Cramér},Q}$ 在 $[1,X]$ 上的值，再零延拓到 $\mathbb F_p$，其中 $32X<p\le64X$。所需的唯一素数输入是

\[
\exists C>0\ \forall X\text{ 充分大}\ \forall p\text{ 素且 }32X<p\le64X,
\qquad \|f\|_{U^5(\mathbb F_p)}^{32}\le C(\log X)^{-1280}. \tag{3}
\]

Green–Sawhney [命题 4.4](https://arxiv.org/abs/2410.04189) 的 $[X]$ 区间估计给出这一输入的纸笔来源。将论文参数取为 $X^2$，并固定 Gowers 阶 5、对数指数 1280。区间支撑内的立方体模 $p$ 不绕回，对应整数立方体。区间的归一化因子是支撑内的立方体数除以 $p^6$，至多 1。`PrimeUniformity.IntervalMoment` 已在 Lean 中证明这个精确等式、归一化因子的上界，以及区间估计推出 (3) 的归约。区间上的定量素数估计仍待证明。

代码选 $T=2^k$、$X=4000k^{14}T$。伴随权重各为 $O(k^2)$，有限域求和的规模是 $O(k^{28}4^k)$，而 (3) 给出 $O(k^{-40})$ 的单因子 Gowers 范数。三角形矩形权的 Fourier 范数为 1。六次替换的误差均为 $O(k^{-2}4^k)$，足以把 Cramér 主项的统一正下界转给真实素数。这些估计及其与原题计数的连接已在 Lean 中证明。

## Lean 接口中的尺度

`Scaled.lean` 只在周长趋于无穷的子序列上证明超线性。取整数尺度 $k$，固定 $Z=k^7$、$T=2^k$，以 $3600000000\,k^{21}4^k$ 为周长上界。因为 $(\log T)^6=(\log 2)^6k^6$，所需单平面下界为 $\gg 4^k/k^6$。参数数为 $\gg k^{28}$，平面两两重合损失至多 $O(k^{56})$。去重后主项为 $\gg k^{22}4^k$，与周长上界的比趋于无穷。

`PrimeWeights.lean` 的 `WeightedPrimeRectangleLowerBound` 把下面的分析结论写成精确前提。对于同一个正数 $c$ 和统一充分大的 $k$，每个参数盒中局部可容许平面的六个素数支持权重乘积之和至少为 $c4^k$。`ModelTransfer.lean` 把这个前提进一步拆成有限 Cramér 模型下界，以及六次逐因子替换的误差 $o(4^k)$。余数矩形误差、有限奇异乘积下界与 Bonferroni 夹逼分别由 `ResidueRectangles.lean`、`Products.lean` 与 `Bonferroni.lean` 给出源码。

## 所需定理与量词

沿用 \(q=1\) 的整数参数构造。设 \(Y\) 是核心周长上界，取 \(Z=(\log Y)^7\) 和 \(T^2=Y/(C_hZ^3)\)。每个保留参数 \(\theta=(\alpha,\beta,\gamma)\) 对应六个整数仿射式 \(\psi_{\theta,i}\colon\mathbb Z^2\to\mathbb Z\)。令 \(\Omega_T\) 为 \(-2T\le r\le-T,\ 0\le s\le10^{-5}T\) 在整数坐标 \((n,m)\) 下的实数原像。

需要如下单平面估计，其中 \(c,T_0\) 必须统一于保留参数。

\[
 \exists c>0\ \exists T_0\ \forall Y\text{ 使 }T\ge T_0\
 \forall \theta\text{ 保留于尺度 }Z,\qquad
 \#\{v\in\Omega_T\cap\mathbb Z^2:
       \ \forall i,\ \psi_{\theta,i}(v)\text{ 为素数}\}
 \ \ge\ c\frac{T^2}{(\log T)^6}. \tag{1}
\]

可以在接口中一并要求六值互异且皆大于 \(127\)。互异性由 (1) 去除 15 条碰撞直线得到，每条包含 \(O(T)\) 个整数点。大于 \(127\) 由构造的正值下界得到。固定 \(T_0\) 再全称量化 \(\theta\) 是关键，逐个固定参数存在不同阈值不足以应用于随 \(Y\) 增加的平面。

## 独立的纸面来源及精确特化

Kravitz–Woo–Xu 的 [《The distribution of prime values of random polynomials》定理 3.1](https://arxiv.org/abs/2512.03292) 第一部分给出统一的普通 von Mangoldt 权重渐近式。该定理正文的[可读副本](https://www.researchgate.net/publication/398313216_The_distribution_of_prime_values_of_random_polynomials) 在第 11–13 页列明系数条件、奇异级数和证明。对固定的 \(d,k,A\)，凸集 \(\Omega\subset[-N,N]^d\) 与 \(k\) 个整数仿射式 \(\psi_i\)，若线性部分两两线性无关，且线性系数、常数项的绝对值皆不超过 \((\log N)^A\)，则

\[
 \sum_{v\in\Omega\cap\mathbb Z^d}\prod_{i=1}^k\Lambda(\psi_i(v))
   = \mathrm{vol}(\Omega)\prod_p\beta_p
     +O_{d,k,A}\bigl(N^d(\log N)^{-A}\bigr),
 \qquad
 \beta_p=(1-p^{-1})^{-k}p^{-d}
 \#\{v\in\mathbb F_p^d:\forall i,\ \psi_i(v)\ne0\}.
 \tag{2}
\]

此处 \(\Lambda(p^a)=\log p\)（\(p\) 素且 \(a\ge1\)），其他正整数上的值为零。用 (2) 时，取 \(d=2,\ k=6,\ A=16,\ N=\lceil C T\rceil\)，其中 \(C\) 是使 \(\Omega_T\subset[-CT,CT]^2\) 的固定常数。参数盒给出全部仿射系数和截距 \(O(Z^2)=O((\log T)^{14})\)，因为 \(\log T\asymp\log Y\)。因此对于统一充分大的 \(T\)，它们都小于 \((\log N)^{16}\)。用十五个不为零的行列式核对线性部条件。换坐标只乘以固定且非零的行列式。

区域面积为 \(c_\Omega T^2\)（\(c_\Omega>0\) 固定），最大坐标值 \(M=O(Z^2T)\)，所有坐标趋于无穷大。保留参数定义保证每个 \(p\nmid W\) 上各式均非零，且 \(p\ge13\)，所以至多六条仿射直线，给出

\[
 \beta_p\ge (1-6/p)(1-1/p)^{-6}.
\]

右边全为正，且与 1 的距离为 \(O(p^{-2})\)。对 \(p\mid W\)，固定合法点给出 \(\beta_p\ge p^{-2}(1-p^{-1})^{-6}\)。两者相乘给出统一正下界。对每个平面，充分大的素数上任意两行独立，每两条零线至多交于一点，因此包含排斥给出 \(\beta_p=1+O(p^{-2})\) 并保证乘积收敛。这里“充分大”的阈值可随平面而异，统一正下界来自前述逐素数下界。

由 (2) 得到总权重 \(\gg T^2\)。剔除非素数的真素数幂如下。最多有 \(\sqrt M\lfloor\log_2M\rfloor\) 个可能值 \(p^a\le M,\ a\ge2\)。每个仿射式非恒定，其每个等值层在 \([-CT,CT]^2\) 内有 \(O(T)\) 个整数点。全体剔除点因此至多 \(O(T\sqrt M\log M)\)，减去的总权重至多

\[
 O\bigl(T\sqrt M(\log M)^7\bigr)
 =O\bigl(T^{3/2}(\log T)^{14}\bigr)=o(T^2).
\]

剩下的全素数点每点权重至多 \((\log M)^6\ll(\log T)^6\)，得到 (1)。这是 [Bienvenu 命题 2.1](https://research-information.bris.ac.uk/files/94726297/WQtrick.pdf) 以外可直接逐项核对的纸面来源。Bienvenu 使用只支持在素数上的权重，可省去剔除真素数幂的一段。

## 可复用的 Lean 范围

检查 plby/lean-proofs 提交 [8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao)。源文件中已有以下通用接口，可作为实现参考。

| 上游文件（相对于 Wikipedia/GreenTao） | 可复用内容 |
|---|---|
| `LinearForms/Geometry.lean` | `AffineForm` 线性部分、`PairwiseIndependentCoefficients`、`CoefficientBound` |
| `Sieve/GoodPrimeAffineRank.lean` | 通过非零二阶子式判定模素数的秩，`pairLinearMapZMod_surjective_of_affineRankTwoGoodPrime`，以及公共零点密度 \(\le p^{-2}\) |
| `Sieve/PairedLocalFactors.lean` | `affineFamilyZeroDensity_eq_card`、单式和双式的零点密度计算 |
| `Sieve/GoodPrimeLocalFactorBound.lean` | `abs_mean_systemLocalCoprimeWeight_sub_firstOrder_le` 与有限包含排斥 |
| `Sieve/EulerProductControl.lean` | `HasPrimeSquareError.multipliable` 和 `HasPrimeSquareError.tprod_ne_zero` |

上游 [`GreenTao.green_tao`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao.lean) 的证明链通过 [`hasStandardCyclicMajorantLinearForms`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/StandardCyclicLinearForms.lean) 控制 Conlon–Fox–Zhao 相对 Szemerédi 方法中的特定 CFZ 线性式。在 [`FinalTransferenceAssembly.lean`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/FinalTransferenceAssembly.lean) 可看到系数由整数 \(k\) 固定，为整个系统选择一个共同的既约剩余类 \(b\)，被估计对象是筛法上界权，而 (1) 计数的是一般六式在实际素数上的权。把该上界权的线性式条件直接作为 (1) 的输入，会遗漏从筛法权到真实素数相关性的估计。

零点几何部分无需引入整套 Green–Tao 包作为依赖。若当前 Mathlib 固定版本与上游对不上，按以上有限仿射接口实现局部因子即可。只有 Lean 内核检验过、无未证前提的 (1) 才能关闭该分析数论缺口。

## 分解无条件分析缺口

Kravitz–Woo–Xu 定理 3.1 的 von Mangoldt 部分可拆成三块。对于固定六式，可以将它们作为独立 Lean 模块的目标。

1. **真实素数的一致性。** 固定任意 \(B>0\)，令 \(z=\exp((\log X)^{1/10})\)，则 \(\|\Lambda-\Lambda_{\mathrm{Cramér},z}\|_{U^5[\pm X]}\ll_B(\log X)^{-B}\)。Leng 的[《Efficient Equidistribution of Nilsequences》](https://arxiv.org/abs/2312.10772) 获得真实权与 Siegel 模型间的误差，Tao–Teräväinen 的 [JEMS 1404 定理 2.5](https://doi.org/10.4171/jems/1404) 控制 Siegel 与 Cramér 两模型的差，Siegel 定理将后者对例外模数的幂次节省转成任意对数幂节省。Kravitz–Woo–Xu 第 3.1 节脚注解释了最后一步。亦可直接采用 Green–Sawhney [《Primes of the form \(p^2+nq^2\)》命题 4.4](https://arxiv.org/abs/2410.04189) 的只支持在素数上的 \(\Lambda'\) 版本，在该命题中令 \(k=5\)，取其区间长度为此处的 \(X\)。偶延拓由三角不等式给出同阶界。采用 \(\Lambda'\) 可省去剔除真素数幂的步骤。两种版本都未找到对应已核验 Lean 源码。
2. **带系数损失的相关性转移。** 对 \(\Omega=\Omega_T\) 和 \(X=O(T(\log T)^{14})\)，六线性式的广义 von Neumann 不等式界定相关和。指定其中一项取 \(U^5[\pm X]\) 范数，其余五项取 \(\ell^\infty\) 范数，系数与截距只损失一个固定对数幂。展开真实权与模型权的差，取足够大的 \(B\) 即得 \(o(T^2)\) 误差。区域是矩形，可以直接按矩形推导该不等式。
3. **模型主项。** Tao–Teräväinen [定理 5.2](https://doi.org/10.4171/jems/1404) 对 Cramér 权的相关和给出奇异级数乘体积，并容许此处系数和截距大小。下面给出本题矩形上的初等下界证明，可省去该一般模型定理。

### 矩形上初等证明 Cramér 模型下界

取 \(X\) 为所有 \(\psi_i\) 值的一个上界，且 \(X\asymp TZ^2\)，按素数一致性定理选 \(z=\exp((\log X)^{1/10})\)。记
\[\Lambda_{\rm Cramér,z}(n)=
 \left(\prod_{p\le z}(1-1/p)^{-1}\right)
 1_{\forall p\le z,\ p\nmid n}.\]
令 \(g(p)\) 为 \(\mathbb F_p^2\) 上六个零点事件的并集密度，令 \(g(d)=\prod_{p\mid d}g(p)\)（\(d\) 无平方因子）。中国剩余定理给出恰好 \(d^2g(d)\) 个剩余类 \((n,m)\pmod d\)，对应“对每个 \(p\mid d\) 至少一个值被 \(p\) 整除”。固定剩余类在 \(\Omega_T\) 的点数为 \(\mathrm{area}(\Omega_T)/d^2+O(T/d+1)\)，因为 \(\Omega_T\) 是轴对齐矩形。记 \(A_d\) 为所有符合该事件的点数，则
\[
  A_d=\mathrm{area}(\Omega_T)g(d)+O(Td+d^2).
\]

取奇数 \(L\) 使 \(L\asymp(\log\log T)^2\)，用截到 \(L\) 项的 Bonferroni 下界。所有有效模数 \(d\) 都不超过 \(D=z^L=T^{o(1)}\)。因此余项累积至多 \(O(TD^2+D^3)=T^{1+o(1)}\)。比较截断主项与完整的 \(\prod_{p\le z}(1-g(p))\) 时，对有限独立 Bernoulli 事件再用一次 Bonferroni。上下截断的差恰为 \(L+1\) 阶初等对称和，至多 \((\sum_{p\le z}g(p))^{L+1}/(L+1)!\)。各式模 \(p\) 非零给出 \(g(p)\le6/p\)。借助 Chebyshev 上界与分部求和，有 \(\sum_{p\le z}g(p)=O(\log\log T)\)。令 \(L\asymp(\log\log T)^2\)，上述差对任意固定 \(B>0\) 都是 \(o((\log T)^{-B})\)。

因此取 \(B\) 大于归一化因子的固定对数增长指数即可。具体而言，Chebyshev 同样给出 \(\prod_{p\le z}(1-1/p)^{-6}=(\log T)^{O(1)}\)。乘上归一化因子后，六式 Cramér 权总和至少为
\[
  \mathrm{area}(\Omega_T)\prod_{p\le z}\beta_p-o(T^2)
  \gg T^2.
\]
此处只用有限奇异乘积的逐素数一致下界。无需对无穷乘积形式化取极限，也无需 Iwaniec 筛的基本引理。

### 矩形上的有限域 Cauchy–Schwarz 转移

选素数 \(P\asymp X\)，令 \(P>32X\)，其中 \(X\) 同时界定坐标矩形的绝对值及六仿射式在矩形中的绝对值。Bertrand 定理足够。任意两行的非零行列式绝对值为 \(O(Z^4)<P\)，故它们在 \(\mathbb F_P^2\) 上仍然线性无关。

将每个一元权函数限制在整数区间 \([-X,X]\) 并以 0 延拓至 \(\mathbb F_P\)。将矩形上的相关和写成 \(\mathbb F_P^2\) 上的和及两个区间指示函数的乘积。两个指示函数分别做 Fourier 展开。对任意不为零的频率 \(u\)，归一化 Fourier 系数的绝对值不超过 \(\min(1,1/(2\min(u,P-u)))\)，由有限等比和与 \(\sin\) 下界得到。零频率不超过 1，故两个区间指示的 Fourier 系数各自的绝对值之和均为 \(O(\log P)\)。对任意展开项，把它的二维加法特征吸收到两个非目标的素数权里。任取两个非目标线性部，它们的独立性使原二维频率可以表达为这两个线性部各自乘某个标量后的和。由仿射常数引入的全局相位模长为 1。

固定目标式 \(i_0\)。依次对其余五式进行方向 Cauchy–Schwarz，每次沿当前消去项的线性部之核。第 \(j\) 次先固定前 \(j-1\) 轮差分参数，因为当前非目标式的全部平移因子沿其核均保持常数。将它们以无穷范数上界消去。核方向在目标线性部上非零，因此最终目标式的五个平移差分均匀遍历 \(\mathbb F_P\)。五轮给出
\[
 \left|\mathbb E_{v\in\mathbb F_P^2}\prod_i f_i(\psi_i(v))\right|
 \le \|f_{i_0}\|_{U^5(\mathbb F_P)}
      \prod_{i\ne i_0}\|f_i\|_\infty.
\]
在 \(P>32X\) 时，所有立方体顶点均在支撑内的模 \(P\) 加法关系都可提升为整数关系。取基点与五个单边端点在 \([-X,X]\) 的代表，整数边长绝对值均不超过 \(2X\)。按这些整数边计算的任意顶点与其短代表相差严格小于 \(P\)，因而两者相等。标准区间归一化下，全群 \(U^5\) 范数为区间 \(U^5\) 范数乘区间指示函数的全群 \(U^5\) 范数，后者至多 1。

合并 Fourier 系数、恢复未归一化相关和，转移损失最多 \(O(P^2(\log P)^2)=T^2(\log T)^{O(1)}\)。对 \(\Lambda\) 与 \(\Lambda_{\rm Cramér,z}\) 剩余五个因子可用一致的对数幂无穷范数上界。用第 1 块的任意 \(B\) 指数，可将六项望远镜展开的总误差降到 \(o(T^2)\)。

Lean 使用三角形权处理矩形。每个坐标权是区间指示的归一化自相关，平移只改变 Fourier 相位，Fourier 系数绝对值和恰为 1。中央子矩形的权重至少为 $1/4$，其 Cramér 主项由任意整数矩形的 CRT 与 Bonferroni 估计得到。由此省去对矩形硬边界的 Fourier 对数界。

### 仅用调和和控制模型筛误差

对 Cramér 模型的主项，Bonferroni 的误差可以先用普通调和和处理。取奇数截断阶 $L\asymp(\log X)^{1/3}$，则 $\sum_{p\le Q}g(p)\ll\log Q\asymp(\log X)^{1/10}$。利用 $j!\ge (j/2)^{\lfloor j/2\rfloor}$，第一项偶截断上界按 $\exp(-cL\log\log X)$ 衰减。最大的截断模数满足 $\log D\ll(\log X)^{13/30}$。因此格点误差乘上粗归一化 $\exp(O(\log Q))$ 仍是 $o(T^2)$。

逐因子替换需要较紧的多对数无穷范数。令 $s=1+1/\log Q$，用 $p^{-1}\le e\,p^{-s}$ 及有限正 Euler 乘积，可将素数倒数和压到 $e\log(1+\log Q)$。只需 $\sum_{n\ge1} n^{-s}\le 1+1/(s-1)$ 的积分比较。这样 Cramér 归一化仍为 $(\log T)^{O(1)}$。
