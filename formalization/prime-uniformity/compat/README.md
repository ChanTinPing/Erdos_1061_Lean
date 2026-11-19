# Lean v4.34.1 上游输入与原题归约

这个目录单独使用 Lean v4.34.1。PrimeUniformity 和 JSP 的默认构建仍使用 v4.33.0。

[UpstreamIntervalNorm.lean](UpstreamIntervalNorm.lean) 直接导入 OAI 的
`SupportedCubeEquivTransport`，将本包的实值区间范数与上游先取复立方体和的实部、
再除以有效立方体数的范数对应。两侧使用相同的底点、步长和有效顶点。
本地用 Lean `v4.34.1`（`5045d0056413266e57c625dcd7c365b10e377c52`）从源码重编了
该 OAI 模块的 23 个依赖闭包模块，并检查了桥接定理。
`#print axioms` 给出 `propext`、`Classical.choice` 和 `Quot.sound`。

固定 [OAI 源码提交](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean)
`4eaee87548250b2682affda7d05d947c05554bae` 和它的
[Mathlib 锁定提交](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612)
`d13f23b723b8a846827a245b89c10fc7d3f11612`。
准备上游锁定依赖及 Mathlib 编译产物后，在上游 `lean/` 目录执行以下 PowerShell 命令。
OAI 依赖的源码保持原样。

```powershell
$env:LEAN_NUM_THREADS = '1'
$env:LEAN_STACK_SIZE_KB = '32768'
lake build +OAI.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
$upstreamLeanPath = lake env powershell.exe -NoProfile -Command '$env:LEAN_PATH'
```

然后在本仓库的 `formalization/prime-uniformity/` 目录按依赖顺序重编九个本地模块。
该闭包在 v4.34.1 下使用本仓库源码即可。

```powershell
$out = Join-Path (Get-Location).Path '.lake/compat-v4.34/lib/lean'
New-Item -ItemType Directory -Path (Join-Path $out 'PrimeUniformity') -Force | Out-Null
$env:LEAN_PATH = "$out;$upstreamLeanPath"
$modules = 'CubeLift', 'Gowers', 'Weights', 'Estimate', 'CubeProduct',
  'GowersSum', 'IntervalMoment', 'IntervalBounds', 'IntervalNorm'
foreach ($name in $modules) {
  elan run leanprover/lean4:v4.34.1 lean -j 1 -o "$out/PrimeUniformity/$name.olean" "PrimeUniformity/$name.lean"
  if ($LASTEXITCODE -ne 0) { throw "Lean failed for $name" }
}
elan run leanprover/lean4:v4.34.1 lean -j 1 compat/UpstreamIntervalNorm.lean
```

桥接文件使用传统导入格式。Lean 的 `module` 文件无法导入采用传统格式的 OAI 源码。
这一步复核区间范数等式。下一节接入完整原生区间逆定理。

## Windows 缓存抽检

[第三方 OAI 编译缓存](https://github.com/nealmcb/openai-math-lean-tooling/blob/main/results/lake-cache-test/README.md)
为同一 OAI 提交提供 Linux 构建产物。在上述固定依赖的 Windows 环境中执行
`lake --no-build --quiet query +OAI.Combinatorics.Progressions.Linear.BasisSurjectionSection:depHash`
得到 `67fdd9bdfac7f95c`。该键在上游修订映射中对应
`a6f48b954a62ed12.ltar`。用 Windows 的 `leantar -x -j -` 解包该文件时，
JSON 输入的 `hash` 取上述键，`base` 的三个目录分别放置 Lean 产物、IR 和其他输出。
Lean 4.34.1 能导入这个缓存模块，并读取 `basisSurjectionSection_rightInverse` 的类型和标准公理列表。
这次抽检只覆盖逆定理依赖闭包中的一个叶模块。

使用同一个隔离缓存，打开 `LAKE_ARTIFACT_CACHE=true` 和
`LAKE_RESTORE_ARTIFACTS=true`，用 `lake cache get --mappings-only` 载入该修订映射后，
下面的命令在 Windows 上从缓存恢复了区间逆定理的完整 OAI 依赖闭包。
`--no-build` 使缺产物的任务报错。此次返回 0，共 11,028 个构建任务，
其中 2,105 个是 OAI 源模块。

```powershell
$env:LEAN_NUM_THREADS = '16'
lake --no-build build +OAI.Combinatorics.Progressions.Lattices.NativeIntegerIntervalInverse
```

首次恢复的逆定理产物为 `dc37cd92b8820e3e.ltar`。随后用 Lean v4.34.1 检查了 [UpstreamNativePrimeTests.lean](UpstreamNativePrimeTests.lean)。它实际导入完整逆定理，为单一的、带级数掩码的原生幂零测试族证明逆定理接口、复杂度单调性和零步条件。逆定理及桥接结论的 `#print axioms` 只列出三个标准公理。上游逆定理的依赖从缓存恢复，尚未在此环境进行整闭包的新内核重放。

从上游目录重新取得包含逆定理产物的 `$upstreamLeanPath`。在本包目录复用前面的 `$out` 和 `LEAN_PATH`，按以下顺序编译桥接依赖。这里使用的都是当前工作树的 Lean 源码。

```powershell
$modules = 'CramerPrimeBlocks', 'Weights', 'CramerNormalization', 'Bonferroni', 'CramerBudget',
  'IndependentSieve', 'ResidueIntervals', 'CramerAP', 'DyadicSieve', 'CramerAPDecay', 'Gowers',
  'CubeProduct', 'GowersSum', 'CubeLift', 'Estimate', 'IntervalMoment', 'IntervalBounds',
  'LogSavings', 'CramerCutoff', 'CutoffDyadicScale', 'IntervalSupport', 'SiegelModel',
  'PrimePowers', 'PrimeProgressions', 'ProgressionComparison', 'ProgressionBoundary',
  'IntervalNorm', 'CramerBoundary', 'StrictCutoffTransfer', 'UpstreamInverseReduction',
  'PrimeProgressionTests', 'CorrelationDescent'
foreach ($name in $modules) {
  elan run leanprover/lean4:v4.34.1 lean -j 1 -o "$out/PrimeUniformity/$name.olean" "PrimeUniformity/$name.lean"
  if ($LASTEXITCODE -ne 0) { throw "Lean failed for $name" }
}
elan run leanprover/lean4:v4.34.1 lean -j 1 -o "$out/PrimeUniformity/UpstreamIntervalNorm.olean" compat/UpstreamIntervalNorm.lean
if ($LASTEXITCODE -ne 0) { throw 'Lean failed for UpstreamIntervalNorm' }
elan run leanprover/lean4:v4.34.1 lean -j 1 compat/UpstreamNativePrimeTests.lean
```

`gowersUniformityEstimate_of_native_prime_descent` 将第五阶估计缩减为 `UniformPrimePrefixEstimate` 和这个具体测试族上的 `PrimeCramerStepDescent 4 nativePrimeTests`。
`nativePrimeTest_topInvariant_drop` 已用上游顶层商验证。若观测函数在最高层平移下不变，就能在同一算术级数上逐点保持求值，同时把测试降低一阶。其复杂度上界是原对数预算的固定多项式。
`nativePrimeTest_correlating_vertical_component` 已接入上游竖直 Fourier 分解。它在保留级数掩码的情况下选出一个有相关性的竖直项，并给出近似误差、项数损失和有理频率高度。
`nativePrimeTest_of_frozen_orbit` 接入了上游的冻结轨道商。给定有复杂度控制的快轨道、冻结的平滑和有理因子及最高层不变性，输出保留级数掩码、范数界和逐点求值的低阶原生测试。

## 算术级数素数输入

同一缓存初次试运行时，`LargeModulusSiegelWalfisz` 的第一个缺少可用产物的外部模块是
`PrimeNumberTheoremAnd.Erdos970.Auxiliary`。随后用标准 Lake 构建了完整的 26 个外部
PNT 模块。使用上游固定的 `PrimeNumberTheoremAnd` 提交
`c39a751132c88b6e8080b74c74023fd95b3d8be0`、`StrongPNT` 提交
`2f5835c322314f55f1026ec2f139d704b7c45c69` 及附带的 v4.34.1 兼容补丁。
本地 Windows 构建使用短路径的隔离工作目录，避免输出路径超过 Windows 工具的长度限制。

在准备好的上游 `lean/` 目录执行以下命令。第一条 Lake 命令构建外部模块，
第二条通过相同的已配置缓存恢复 135 个 OAI 算术模块。

```powershell
$env:LEAN_NUM_THREADS = '2'
$pntModules = '+PrimeNumberTheoremAnd.Erdos970.Consequences',
  '+PrimeNumberTheoremAnd.Erdos970.HadamardSupport',
  '+PrimeNumberTheoremAnd.Erdos970.MertensClassical',
  '+StrongPNT.Erdos970.PNT5_Strong'
lake --no-cache build @pntModules
if ($LASTEXITCODE -ne 0) { throw 'External PNT build failed' }
$env:LAKE_ARTIFACT_CACHE = 'true'
$env:LAKE_RESTORE_ARTIFACTS = 'true'
$env:LEAN_NUM_THREADS = '16'
lake --no-build build +OAI.NumberTheory.Jacobsthal.Sieve.LargeModulusSiegelWalfisz
if ($LASTEXITCODE -ne 0) { throw 'OAI prime prefix cache restore failed' }
$upstreamLeanPath = lake env powershell.exe -NoProfile -Command '$env:LEAN_PATH'
```

在本包目录复用前面已经编译的本地 `PrimeUniformity.PrimeProgressions` 和 `$out`，
用实际包含 OAI 定理及外部 PNT 模块的 `LEAN_PATH` 检查。

```powershell
$env:LEAN_PATH = "$out;$upstreamLeanPath"
$env:LEAN_NUM_THREADS = '1'
elan run leanprover/lean4:v4.34.1 lean -j 1 compat/UpstreamPrimePrefix.lean
```

[UpstreamPrimePrefix.lean](UpstreamPrimePrefix.lean) 已实际导入 `residuePsi_exponential`，
并推出 `upstream_uniformPrimePrefix : UniformPrimePrefixEstimate`。
后者及实际导入的上游定理均通过 `#print axioms` 检查，
只列出 `propext`、`Classical.choice` 和 `Quot.sound`。
OAI 算术模块来自缓存，本地从源码编译了 26 个外部依赖。
## 同一工具链中的原题入口

[UpstreamFixedEstimate.lean](UpstreamFixedEstimate.lean) 同时导入原生逆定理和算术级数入口。`gowersUniformityEstimate_of_native_step_descent` 只接受 `PrimeCramerStepDescent 4 nativePrimeTests`，直接给出本题需要的五阶估计。

[UpstreamJspReduction.lean](../../jsp-000881/compat/UpstreamJspReduction.lean) 将该估计接到 Erdős #1061 的有序解计数。最终定理 `Jsp000881.not_linear_asymptotic` 直接使用已经验证的两个 Vaughan 分支。`#print axioms` 对完整定理只列出 `propext`、`Classical.choice` 和 `Quot.sound`。

[UpstreamVerticalDescent.lean](UpstreamVerticalDescent.lean) 验证了选取竖直 Fourier 项时的误差和复杂度预算，并用顶层商处理零频率。`not_linear_asymptotic_of_native_vertical_step_descent` 因此只接受 `NativePrimeVerticalStepDescent 4`。这个参数要求在非零竖直频率下找到相关性仍足够大的低阶测试。该入口已实际导入两条上游定理并通过公理检查。

复现完整入口时，按前文准备固定版本的 OAI 和外部依赖。在同一份 OAI 检出的 `lean/` 目录构建或恢复以下三个模块，并取得其 Lean 导入路径。

```powershell
lake build `
  +OAI.Combinatorics.Progressions.Lattices.NativeIntegerIntervalInverse `
  +OAI.Combinatorics.Progressions.Lattices.NativePairAffineCellStepDrop `
  +OAI.NumberTheory.Jacobsthal.Sieve.LargeModulusSiegelWalfisz
$upstreamLeanPath = lake env pwsh -NoProfile -Command '$env:LEAN_PATH'
```

切换到本仓库根目录，用 [Build-CompatProof.ps1](Build-CompatProof.ps1) 按导入顺序编译本地证明闭包。

```powershell
pwsh -NoProfile -File formalization/prime-uniformity/compat/Build-CompatProof.ps1 `
  -ProjectRoot . -UpstreamLeanPath $upstreamLeanPath
```

脚本在 `formalization/prime-uniformity/.lake/compat-v4.34-final/lib/lean` 写入产物。最后编译 `UpstreamJspReduction.lean`，同时打印 `Jsp000881.not_linear_asymptotic` 的公理依赖。附加 `-PlanOnly` 可查看模块和产物路径。

## 伸缩相关到水平系数

[UpstreamTypeI.lean](UpstreamTypeI.lean) 验证自然数区间上的 Type I 平均满足上游仿射胞腔因子分解的输入。结论仅撤去级数步长，保留乘法伸缩参数用于稠密族回收。

[UpstreamTypeISamples.lean](UpstreamTypeISamples.lean) 把 Vaughan 的稠密 Type I 前缀相关转成实际原生伸缩因子族。它沿每个乘法纤维重新索引算术级数，并为保留的因子同时选出一个快子代数和一个分母。此结果已在 v4.34.1 检查。

[UpstreamTypeII.lean](UpstreamTypeII.lean) 对两条伸缩后的原生测试验证同样的接口。第二条取共轭，对应竖直频率取负。归一化列相关推出同一物理尺度上的成对符号分解。

[UpstreamTypeIISamples.lean](UpstreamTypeIISamples.lean) 从相关性大的 Vaughan 二进块构造稠密的伸缩对，使每对都满足这个原生分解接口。输入尺度和损失由 [PrimeCorrelationScale.lean](../PrimeUniformity/PrimeCorrelationScale.lean) 控制。此结果已用实际的上游胞腔定理在 v4.34.1 检查。

[UpstreamTypeIIProjection.lean](UpstreamTypeIIProjection.lean) 从上游的秩敏感水平投影抽出固定消去行的系数约束。给定有界、已清分母的消去行与乘积坐标符号，得到两个伸缩因子按各自幂次分离的近整数式，误差保留原有的次数尺度。

[UpstreamTypeIISymbols.lean](UpstreamTypeIISymbols.lean) 将这个投影计算接到实际成对轨道的符号。分别按两条坐标轴展开对数后，第二条轨道的共轭对应负频率。分离恒等式和近整数误差界均已在 v4.34.1 检查。

[UpstreamTypeIIAxisRows.lean](UpstreamTypeIIAxisRows.lean) 验证单轴快层的原像表示、未饱和单轴的顶层频率消去、轴包含坐标高度和商映射后的精确行核。四条定理已在 v4.34.1 检查。

[UpstreamTypeIIAxisSaturation.lean](UpstreamTypeIIAxisSaturation.lean) 允许两个轴各自存在秩二误差。所得单轴层随次数递减且在 Lie 括号下闭合，有受控的有理基。顶次数、顶秩 Lie 树的频率消去由成对快层传到该单轴层，已在 v4.34.1 检查。

[UpstreamTypeIIPairedQuotientRows.lean](UpstreamTypeIIPairedQuotientRows.lean) 从给定有界生成元选取实际的成对消去行，验证其环境坐标、单轴饱和核以及实际实化符号上的行读数。此结果已在 v4.34.1 检查。

[UpstreamTypeIProjection.lean](UpstreamTypeIProjection.lean) 使用同一投影的单坐标嵌入给出单个伸缩因子的近整数式，并验证有理行的有限分母清除。[UpstreamAnnihilatorRows.lean](UpstreamAnnihilatorRows.lean) 从给定的公共数据构造有界有理行，其核恰为公共四坐标空间。这些接口均已在 v4.34.1 检查。

[UpstreamTypeIQuotientRows.lean](UpstreamTypeIQuotientRows.lean) 从满足高度界的单轨道生成元构造有界消去行。定理同时给出环境空间上的行映射及其精确公共核，即快子空间与第二秩层之和，并把它的有理坐标逐条与投影行对应。

[UpstreamTypeIRowLift.lean](UpstreamTypeIRowLift.lean) 把实际轨道的投影符号行读数逐条等同于轨道对数系数上的实化环境坐标，并保留环境坐标的高度界与核等式。此结果已在 v4.34.1 检查。

[UpstreamTypeIRowRecovery.lean](UpstreamTypeIRowRecovery.lean) 从具有公共因子的稠密伸缩族取得逐行近整数约束，在显式的 Weyl 尺度条件下恢复原轨道的未伸缩行坐标。所得公共分母计入了每行的清分母乘数。此结果已在 v4.34.1 检查。

[UpstreamTypeIRankReassembly.lean](UpstreamTypeIRankReassembly.lean) 从给定的光滑系数、有理系数和剩余系数的层归属构造精确的原生轨道分解。分解保留光滑系数界、有理因子的公共分母，以及其余两个因子的第二秩层和快层归属。通用重组也可接受给定的次数层，供 Type II 的饱和层使用。两项接口已在 v4.34.1 检查。

[UpstreamTypeIOrbitRecovery.lean](UpstreamTypeIOrbitRecovery.lean) 将稠密伸缩族的实际投影行估计接到 Weyl 回收、系数提升和原轨道重组。它得到精确归一化分解、光滑界、秩二与快层归属，并控制有理分母。此结果已在 v4.34.1 检查。

[UpstreamTypeICoefficientLift.lean](UpstreamTypeICoefficientLift.lean) 从有限个近整数行坐标构造轨道重建需要的光滑系数和有理系数。在给定行映射的核等式和高度控制后，得到原生基上的光滑界与分母格，并把系数残差约束在快层与第二秩层之和。此结果已在 v4.34.1 检查。

[UpstreamCommonDilationFactors.lean](UpstreamCommonDilationFactors.lean) 在给定同一适配基的伸缩族中选出公共快子代数和有理分母，保留原有因子分解和最高层频率约束。保留的伸缩下标至少占原集合的 `exp(-((p + 2)^5 + p))`。此结果已在 v4.34.1 检查。

[UpstreamCommonAdaptedBasis.lean](UpstreamCommonAdaptedBasis.lean) 先从各伸缩因子各自的有界适配基中选出共同基和权重，再应用公共快子代数和分母的选取。结论保留每个伸缩因子的分解证书和显式的子集基数下界，已在 v4.34.1 检查。

[UpstreamDescentCorrelation.lean](UpstreamDescentCorrelation.lean) 在原测试的算术级数内选取短区间和细分剩余类，冻结光滑因子及有理因子。给定快轨道的实现与顶层频率消去，得到低一步的原生测试，并明确计入冻结误差和细分单元数。此结果已在 v4.34.1 检查。

[UpstreamFastOrbitRealization.lean](UpstreamFastOrbitRealization.lean) 将归一化轨道提升到受控的快子代数重过滤模型，保持映回原模型的逐点求值，并把快子代数的最高层频率消去传到这个实现。其输入是实际轨道的对数系数归属，已在 v4.34.1 检查。

[UpstreamRankOneFastEnlargement.lean](UpstreamRankOneFastEnlargement.lean) 在顶层秩为一时将第二秩层并入快层。它验证扩充过滤的括号闭合、有界层基、原生模型复杂度、乘积轨道的精确求值及最高层频率消去，已在 v4.34.1 检查。

[UpstreamFastRankLift.lean](UpstreamFastRankLift.lean) 在一般秩下从有界层生成元构造原生自由秩模型及实际轨道提升。它保留格覆盖和逐点求值，并将顶次数、顶秩 Lie 树的频率消去传给自由模型的最高秩子群。Type I 的快层与秩二因子有专门的接口。此结果已在 v4.34.1 检查。

[UpstreamPrimeRankIteration.lean](UpstreamPrimeRankIteration.lean) 为原生测试初始化正则秩，在最高秩子群不变时构造精确保值的降秩商，并在秩零时去掉最高次数层。统一的单次降秩定理 `NativePrimeRankStepDescent` 因此足以推出原题所需的逐步降阶。此结果已在 v4.34.1 检查。

[UpstreamRankedDescentCorrelation.lean](UpstreamRankedDescentCorrelation.lean) 在保留原次数和秩的情况下冻结归一化外因子并细分算术级数。只要快轨道满足顶秩频率消去，选出的原生测试就具有可送入降秩商的顶秩不变性，并给出相关性的定量转移不等式。此结果已在 v4.34.1 检查。

[UpstreamRankedFreezingBudget.lean](UpstreamRankedFreezingBudget.lean) 定量选择冻结区间长度并计算细分单元数，吸收严格 prime–Cramér 权重与冻结误差。从给定的归一化因子和顶秩消去证书得到实际低一秩的测试，其相关性仍超过相应指数下界。此结果已在 v4.34.1 检查。

[UpstreamPrimeRankAdapted.lean](UpstreamPrimeRankAdapted.lean) 在保留逐点求值的情况下归一化基点并选取秩适配基。它也将固定截止值的 Vaughan 二择直接应用于带算术级数掩码的原生测试。三条定理均已在 v4.34.1 检查。

[UpstreamPrimePreparedRankStep.lean](UpstreamPrimePreparedRankStep.lean) 将这些准备步骤、保轨道的 Fourier 选取和实际 Vaughan 二择接到降秩。顶秩频率为零时直接使用保值的秩商。统一的多项式预算将余下输入约束在顶秩频率非零的归一化测试。此结果已在 v4.34.1 检查。

[UpstreamTypeIRankDrop.lean](UpstreamTypeIRankDrop.lean) 将 Type I 的精确轨道分解接到快模型、冻结及保值商。给定快层的有界基和顶秩消去，它从原来的实际测试构造低一秩的原生测试，并给出相关性下界。此结果已在 v4.34.1 检查。

[UpstreamTypeIIRowConstraints.lean](UpstreamTypeIIRowConstraints.lean) 从共享的成对符号分解得到固定行乘数和统一的近整数误差界，供未伸缩系数的 Weyl 回收使用。此结果已在 v4.34.1 检查。

[UpstreamTypeIIRankDrop.lean](UpstreamTypeIIRankDrop.lean) 将 Type II 的三个归一化因子、有界层基和顶秩 Lie 括号消去接到实际降秩。结论保留严格 prime–Cramér 相关性的定量下界，已在 v4.34.1 检查。

[UpstreamTypeIFromVaughan.lean](UpstreamTypeIFromVaughan.lean) 从共享的分次快子代数生成元选取原生快层的有界生成元和基，并构造与原轨道对数对应的实际消去行。两条定理已在 v4.34.1 检查。

[UpstreamTypeINativeFactorTransport.lean](UpstreamTypeINativeFactorTransport.lean) 验证实际伸缩后的分解可沿次数过滤等式传到秩过滤所用的符号，供同一公共伸缩族的逐行恢复使用。此结果已在 v4.34.1 检查。

[UpstreamTypeIICommonSamples.lean](UpstreamTypeIICommonSamples.lean) 从实际 Vaughan Type II 的成对样本选出共享适配基、快子代数和有理分母。保留成对分解、频率消去及相对于完整二进区间的显式密度界，已在 v4.34.1 检查。

[UpstreamPrimePreparedRankBranches.lean](UpstreamPrimePreparedRankBranches.lean) 将两个逐次数的 Vaughan 分支处理定理合并成统一的单步降秩接口，再接到整体原生下降定理。不同分支的最终指数和阈值可以分别选择。两项归约已在 v4.34.1 检查。

[UpstreamTypeIIAxisRowIdentity.lean](UpstreamTypeIIAxisRowIdentity.lean) 将成对符号的未伸缩行读数等同于原轨道对数在两条单轴上的实系数。两条恒等式已在 v4.34.1 检查。

[UpstreamTypeICommonRows.lean](UpstreamTypeICommonRows.lean) 从同一个 Type I 快子代数同时选择各次数的有界消去行，并将每一行对应到原生轨道的实际系数。此结果已在 v4.34.1 检查。

[UpstreamTypeICommonOrbitRecovery.lean](UpstreamTypeICommonOrbitRecovery.lean) 将同一快子代数的实际伸缩分解和有界行接到原轨道的归一化分解，保留 Weyl 回收所需的尺度前提。此结果已在 v4.34.1 检查。

[UpstreamTypeIIPairedGenerators.lean](UpstreamTypeIIPairedGenerators.lean) 由真实的共享快子代数构造有界成对生成元、原轨道单轴饱和层的有界基，以及各次数的公共消去行。三条定理已在 v4.34.1 检查。

[UpstreamTypeIICommonRows.lean](UpstreamTypeIICommonRows.lean) 由真实公共分解得到成对的近整数约束，同时给出第一坐标行的精确饱和核和原轨道系数恒等式。此结果已在 v4.34.1 检查。

[UpstreamTypeIIProjectionBudget.lean](UpstreamTypeIIProjectionBudget.lean) 用同一个对数尺度控制 Type II 样本损失、行高度、清分母乘数和近整数误差。此结果已在 v4.34.1 检查。

[UpstreamTypeIFromVaughanSamples.lean](UpstreamTypeIFromVaughanSamples.lean) 将实际带级数掩码的 Vaughan Type I 前缀代入原轨道恢复，建立二进区间、公共因子及顶层频率消去。此结果已在 v4.34.1 检查。

[UpstreamTypeIIOrbitRecovery.lean](UpstreamTypeIIOrbitRecovery.lean) 将未伸缩行的近整数估计提升为原轨道的三个归一化因子。中间因子留在第一坐标饱和层，顶秩李括号频率消去；分母及光滑误差保留定量估计。三条定理已在 v4.34.1 检查。

[UpstreamBranchBudget.lean](UpstreamBranchBudget.lean) 将任意固定的自然系数多项式损失控制在分支可用的对数尺度，并在放宽复杂度预算时保留原生测试的逐点求值和相关性下界。三条定理已在 v4.34.1 检查。

[UpstreamTypeIBranchFinish.lean](UpstreamTypeIBranchFinish.lean) 与 [UpstreamTypeIIBranchFinish.lean](UpstreamTypeIIBranchFinish.lean) 分别验证如何用多项式预算下的归一化因子完成各自的 Vaughan 分支，输出实际的低一秩测试。两条收尾定理已在 v4.34.1 检查。

[UpstreamTypeIEventualOrbitRecovery.lean](UpstreamTypeIEventualOrbitRecovery.lean) 将统一的 Type I 公共分母和未伸缩系数估计提升到原生轨道的四因子分解，保留归一化和秩层归属。此结果已在 v4.34.1 检查。

[UpstreamTypeIIVaughanFactors.lean](UpstreamTypeIIVaughanFactors.lean) 从实际带掩码的 Vaughan Type II 块构造满足降秩条件的原轨道因子，并把显式尺度界统一成对数多项式预算。此结果已在 v4.34.1 检查。

[UpstreamTypeIIVaughanBranch.lean](UpstreamTypeIIVaughanBranch.lean) 证明实际 Type II Vaughan 分支 `native_prime_prepared_typeII_branch`。多项式预算满足单步降秩接口，端到端检查仅列出标准公理。

[UpstreamTypeIVaughanOrbits.lean](UpstreamTypeIVaughanOrbits.lean) 和 [UpstreamTypeIUniformFromVaughan.lean](UpstreamTypeIUniformFromVaughan.lean) 从实际 Type I 的前缀伸缩族恢复归一化因子，并证明单步降秩接口 `native_prime_prepared_typeI_branch`。端到端检查仅列出标准公理。

[UpstreamTypeICommonNear.lean](UpstreamTypeICommonNear.lean) 把同一快子代数的伸缩分解直接写成原轨道系数上的近整数不等式，并给出原生快层的有界基。此结果已在 v4.34.1 检查。
