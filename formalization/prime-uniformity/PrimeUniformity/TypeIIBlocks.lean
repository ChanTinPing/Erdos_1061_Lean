module

public import PrimeUniformity.Bilinear
public import PrimeUniformity.PrimeCorrelation
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators ComplexConjugate

/-- Restrict the factor interval to the dyadic block starting at `2^j`. -/
def dyadicFactorBlock (U X j : ℕ) : Finset ℕ :=
  (Finset.Ioc U X).filter (fun n => Nat.log 2 n = j)

theorem mem_dyadicFactorBlock {U X j n : ℕ} :
    n ∈ dyadicFactorBlock U X j ↔ U < n ∧ n ≤ X ∧ 2 ^ j ≤ n ∧ n < 2 ^ (j + 1) := by
  rw [dyadicFactorBlock, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hnU, hnX⟩, rfl⟩
    exact ⟨hnU, hnX, Nat.pow_log_le_self 2 (Nat.zero_lt_of_lt hnU).ne',
      Nat.lt_pow_succ_log_self (by decide) n⟩
  · rintro ⟨hnU, hnX, hlo, hhi⟩
    refine ⟨⟨hnU, hnX⟩, le_antisymm ?_ ?_⟩
    · apply Nat.lt_succ_iff.mp
      exact (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr hhi
    · exact (Nat.le_log_iff_pow_le (by decide) (Nat.zero_lt_of_lt hnU).ne').mpr hlo

theorem card_dyadicFactorBlock_le (U X j : ℕ) :
    (dyadicFactorBlock U X j).card ≤ 2 ^ j := by
  have hsub : dyadicFactorBlock U X j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)) :=
    fun _ hn => Finset.mem_Ico.mpr (mem_dyadicFactorBlock.mp hn).2.2
  simpa only [Nat.card_Ico, pow_succ, Nat.mul_two, Nat.add_sub_cancel_left] using
    Finset.card_le_card hsub

theorem dyadicFactorBlock_eq_Icc (U X j : ℕ) :
    dyadicFactorBlock U X j =
      Finset.Icc (max (U + 1) (2 ^ j)) (min X (2 ^ (j + 1) - 1)) := by
  have hupper : 0 < (2 : ℕ) ^ (j + 1) := by positivity
  ext n
  simp only [mem_dyadicFactorBlock, Finset.mem_Icc, max_le_iff, le_min_iff]
  omega

/-- Partition a positive factor interval by its binary logarithm. -/
theorem sum_eq_dyadicFactorBlocks {R : Type*} [AddCommMonoid R] (U X : ℕ) (f : ℕ → R) :
    ∑ n ∈ Finset.Ioc U X, f n =
      ∑ j ∈ Finset.range (Nat.log 2 X + 1), ∑ n ∈ dyadicFactorBlock U X j, f n := by
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro n hn
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (Finset.mem_Ioc.mp hn).2))

/-- The kernel includes the mask on products. It can enforce both interval
endpoints and a congruence in the Type II residue descent. -/
def vaughanTypeIIKernel (A : Finset ℕ) (F : ℕ → ℂ) (d m : ℕ) : ℂ :=
  if d * m ∈ A then F (d * m) else 0

noncomputable def vaughanTypeIIBlock (X U V i j : ℕ) (A : Finset ℕ) (F : ℕ → ℂ) : ℂ :=
  ∑ d ∈ dyadicFactorBlock U X i, ∑ m ∈ dyadicFactorBlock V X j,
    (ArithmeticFunction.moebius d : ℂ) * (vaughanTypeIIRight V m : ℂ) * vaughanTypeIIKernel A F d m

/-- A nonzero Type II block has a product of lower endpoints at most
the ambient length, because at least one product is in the test support. -/
theorem dyadic_product_le_of_vaughanTypeIIBlock_ne_zero {X U V i j : ℕ}
    {A : Finset ℕ} (hA : A ⊆ Finset.Ioc 0 X) {F : ℕ → ℂ}
    (h : vaughanTypeIIBlock X U V i j A F ≠ 0) :
    2 ^ i * 2 ^ j ≤ X := by
  by_contra! hX
  apply h
  unfold vaughanTypeIIBlock
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro m hm
  have hprod : X < d * m :=
    hX.trans_le (Nat.mul_le_mul (mem_dyadicFactorBlock.mp hd).2.2.1
      (mem_dyadicFactorBlock.mp hm).2.2.1)
  have hnot : d * m ∉ A := fun hmA => (not_le_of_gt hprod) (Finset.mem_Ioc.mp (hA hmA)).2
  simp [vaughanTypeIIKernel, hnot]

/-- Bound the block correlation by the product of the actual row and column
counts, including the logarithmic bound for the Vaughan coefficient. -/
theorem norm_vaughanTypeIIBlock_le_card_mul {X U V i j : ℕ} (hX : 0 < X)
    (A : Finset ℕ) (F : ℕ → ℂ) (hF : ∀ n ∈ A, ‖F n‖ ≤ 1) :
    ‖vaughanTypeIIBlock X U V i j A F‖ ≤ (dyadicFactorBlock U X i).card *
      ((dyadicFactorBlock V X j).card : ℝ) * Real.log (X : ℝ) := by
  let s := dyadicFactorBlock U X i
  let t := dyadicFactorBlock V X j
  let L := Real.log (X : ℝ)
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hX)
  have hpoint (d m : ℕ) (hm : m ∈ t) :
      ‖(ArithmeticFunction.moebius d : ℂ) * (vaughanTypeIIRight V m : ℂ) *
        vaughanTypeIIKernel A F d m‖ ≤ L := by
    have hμ : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    have hV := vaughanTypeIIRight_bounds V m
    have hm' := mem_dyadicFactorBlock.mp hm
    have hΛ : ‖(vaughanTypeIIRight V m : ℂ)‖ ≤ L := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hV.1]
      exact hV.2.trans (Real.log_le_log (by exact_mod_cast Nat.zero_lt_of_lt hm'.1)
        (by exact_mod_cast hm'.2.1))
    have hK : ‖vaughanTypeIIKernel A F d m‖ ≤ 1 := by
      unfold vaughanTypeIIKernel
      split
      · exact hF _ ‹d * m ∈ A›
      · simp
    simp only [norm_mul]
    calc
      _ ≤ (1 * L) * 1 := mul_le_mul (mul_le_mul hμ hΛ (norm_nonneg _) zero_le_one) hK
        (norm_nonneg _) (mul_nonneg zero_le_one hL)
      _ = _ := by simp
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _d ∈ s, ∑ _m ∈ t, L :=
      Finset.sum_le_sum fun d _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => hpoint d m hm)
    _ = (s.card : ℝ) * t.card * L := by simp [nsmul_eq_mul, mul_assoc]

/-- The dyadic factor widths bound the block correlation. -/
theorem norm_vaughanTypeIIBlock_le {X U V i j : ℕ} (hX : 0 < X)
    (A : Finset ℕ) (F : ℕ → ℂ) (hF : ∀ n ∈ A, ‖F n‖ ≤ 1) :
    ‖vaughanTypeIIBlock X U V i j A F‖ ≤ (2 : ℝ) ^ i * 2 ^ j * Real.log (X : ℝ) := by
  have hs : ((dyadicFactorBlock U X i).card : ℝ) ≤ 2 ^ i := by
    exact_mod_cast card_dyadicFactorBlock_le U X i
  have ht : ((dyadicFactorBlock V X j).card : ℝ) ≤ 2 ^ j := by
    exact_mod_cast card_dyadicFactorBlock_le V X j
  exact (norm_vaughanTypeIIBlock_le_card_mul hX A F hF).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul hs ht (Nat.cast_nonneg _) (by positivity))
      (Real.log_nonneg (by exact_mod_cast hX)))

theorem vaughanTypeIICorrelation_eq_dyadicBlocks (X U V : ℕ) (A : Finset ℕ) (F : ℕ → ℂ) :
    vaughanTypeIICorrelation X U V A F =
      ∑ i ∈ Finset.range (Nat.log 2 X + 1), ∑ j ∈ Finset.range (Nat.log 2 X + 1),
        vaughanTypeIIBlock X U V i j A F := by
  rw [vaughanTypeIICorrelation, sum_eq_dyadicFactorBlocks]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [sum_eq_dyadicFactorBlocks V X]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro m _
  by_cases h : d * m ∈ A <;> simp [vaughanTypeIIKernel, h]

/-- If the complete Vaughan Type II term is large, some dyadic block
retains the correlation after losing only the square of the block count. -/
theorem exists_large_vaughanTypeIIBlock {X U V : ℕ} {A : Finset ℕ} {F : ℕ → ℂ}
    {B : ℝ} (hB : ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 2 * B < ‖vaughanTypeIICorrelation X U V A F‖) :
    ∃ i ≤ Nat.log 2 X, ∃ j ≤ Nat.log 2 X, B < ‖vaughanTypeIIBlock X U V i j A F‖ := by
  contrapose! hB
  rw [vaughanTypeIICorrelation_eq_dyadicBlocks]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _i ∈ Finset.range (Nat.log 2 X + 1), ∑ _j ∈ Finset.range (Nat.log 2 X + 1), B := by
      apply Finset.sum_le_sum
      intro i hi
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
      exact hB i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    _ = _ := by simp [nsmul_eq_mul, pow_two, mul_assoc]

/-- In a dyadic Type II block, Cauchy–Schwarz eliminates the Möbius and
von Mangoldt divisor coefficients with explicit logarithmic loss. -/
theorem vaughanTypeIIBlock_pow_four_le (X U V i j : ℕ) (A : Finset ℕ) (F : ℕ → ℂ) :
    let s := dyadicFactorBlock U X i
    let t := dyadicFactorBlock V X j
    let K := vaughanTypeIIKernel A F
    ‖vaughanTypeIIBlock X U V i j A F‖ ^ 4 ≤
      (s.card : ℝ) ^ 2 * ((t.card : ℝ) * Real.log (X : ℝ) ^ 2) ^ 2 *
        ∑ m ∈ t, ∑ m' ∈ t, ‖∑ d ∈ s, K d m * conj (K d m')‖ ^ 2 := by
  intro s t K
  let a (d : ℕ) := (ArithmeticFunction.moebius d : ℂ)
  let b (m : ℕ) := (vaughanTypeIIRight V m : ℂ)
  have ha : (∑ d ∈ s, ‖a d‖ ^ 2) ≤ (s.card : ℝ) := by
    calc
      _ ≤ ∑ _d ∈ s, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d _
        have h : ‖a d‖ ≤ 1 := by
          dsimp only [a]
          rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
        exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (one_pow 2)
      _ = _ := by simp
  have hb : (∑ m ∈ t, ‖b m‖ ^ 2) ≤ (t.card : ℝ) * Real.log (X : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _m ∈ t, Real.log (X : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro m hm
        have ⟨hmV, hmX, _⟩ := mem_dyadicFactorBlock.mp hm
        have hb := vaughanTypeIIRight_bounds V m
        have hm₀ : (0 : ℝ) < m := by exact_mod_cast Nat.zero_lt_of_lt hmV
        have hx : (m : ℝ) ≤ X := by exact_mod_cast hmX
        have h : ‖b m‖ ≤ Real.log (X : ℝ) := by
          dsimp only [b]
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
          exact hb.2.trans (Real.log_le_log hm₀ hx)
        exact pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = _ := by simp [nsmul_eq_mul]
  refine (norm_bilinear_sum_pow_four_le s t a b K).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => sq_nonneg _) ha 2)
      (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => sq_nonneg _) hb 2) (sq_nonneg _) (sq_nonneg _))
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- A sufficiently correlated dyadic block yields many column pairs for
the residue-class and dilation arguments. -/
theorem dense_vaughanTypeIIBlock_columns {X U V i j : ℕ} (hX : 1 < X)
    (A : Finset ℕ) (F : ℕ → ℂ) (hF : ∀ n ∈ A, ‖F n‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) :
    let s := dyadicFactorBlock U X i
    let t := dyadicFactorBlock V X j
    let K := vaughanTypeIIKernel A F
    s.Nonempty → t.Nonempty →
    (s.card : ℝ) ^ 2 * ((t.card : ℝ) * Real.log (X : ℝ) ^ 2) ^ 2 *
      (δ * (s.card : ℝ) ^ 2 * (t.card : ℝ) ^ 2) ≤ ‖vaughanTypeIIBlock X U V i j A F‖ ^ 4 →
    (δ / 2) * (t.card : ℝ) ^ 2 ≤
      (((t ×ˢ t).filter (fun p : ℕ × ℕ => (δ / 2) * (s.card : ℝ) ≤
        ‖∑ d ∈ s, K d p.1 * conj (K d p.2)‖)).card : ℝ) := by
  intro s t K hs ht hlarge
  apply dense_large_column_correlations s t hs K hδ
  · intro d _ m _
    dsimp only [K, vaughanTypeIIKernel]
    split
    · exact hF _ ‹d * m ∈ A›
    · simp
  · have hs' : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
    have ht' : (0 : ℝ) < t.card := Nat.cast_pos.mpr ht.card_pos
    have hl : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
    have hpref : 0 < (s.card : ℝ) ^ 2 * ((t.card : ℝ) * Real.log (X : ℝ) ^ 2) ^ 2 :=
      mul_pos (pow_pos hs' _) (pow_pos (mul_pos ht' (pow_pos hl _)) _)
    exact (mul_le_mul_iff_right₀ hpref).mp (hlarge.trans (vaughanTypeIIBlock_pow_four_le X U V i j A F))

end PrimeUniformity
