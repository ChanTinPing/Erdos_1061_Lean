module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators

/-- The part of an arithmetic function supported on indices at most the cutoff. -/
def arithmeticLowCutoff {R : Type*} [Zero R] (U : ℕ) (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨fun n => if n ≤ U then f n else 0, by simp⟩

/-- The part of an arithmetic function supported on indices above the cutoff. -/
def arithmeticHighCutoff {R : Type*} [Zero R] (U : ℕ) (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨fun n => if U < n then f n else 0, by simp⟩

theorem arithmeticLowCutoff_apply {R : Type*} [Zero R] (U : ℕ)
    (f : ArithmeticFunction R) (n : ℕ) :
    arithmeticLowCutoff U f n = if n ≤ U then f n else 0 :=
  rfl

theorem arithmeticHighCutoff_apply {R : Type*} [Zero R] (U : ℕ)
    (f : ArithmeticFunction R) (n : ℕ) :
    arithmeticHighCutoff U f n = if U < n then f n else 0 :=
  rfl

theorem arithmeticLowCutoff_add_highCutoff {R : Type*} [AddMonoid R] (U : ℕ)
    (f : ArithmeticFunction R) :
    arithmeticLowCutoff U f + arithmeticHighCutoff U f = f := by
  ext n
  by_cases hn : n ≤ U
  · simp [arithmeticLowCutoff_apply, arithmeticHighCutoff_apply, hn, not_lt_of_ge hn]
  · simp [arithmeticLowCutoff_apply, arithmeticHighCutoff_apply, hn, lt_of_not_ge hn]

/-- The coefficient supported up to the product of the two Vaughan cutoffs. -/
noncomputable def vaughanTypeICoefficient (U V : ℕ) : ArithmeticFunction ℝ :=
  arithmeticLowCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
    arithmeticLowCutoff V ArithmeticFunction.vonMangoldt

/-- The von Mangoldt divisor sum over divisors above the second Vaughan cutoff. -/
noncomputable def vaughanTypeIIRight (V : ℕ) : ArithmeticFunction ℝ :=
  arithmeticHighCutoff V ArithmeticFunction.vonMangoldt * ArithmeticFunction.zeta

/-- Vaughan's identity as an exact equality of Dirichlet convolutions. -/
theorem vonMangoldt_eq_vaughan (U V : ℕ) :
    ArithmeticFunction.vonMangoldt =
      arithmeticLowCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
          ArithmeticFunction.log +
        arithmeticLowCutoff V ArithmeticFunction.vonMangoldt -
        vaughanTypeICoefficient U V * ArithmeticFunction.zeta +
        arithmeticHighCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
          vaughanTypeIIRight V := by
  let M : ArithmeticFunction ℝ := ArithmeticFunction.moebius
  let Z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
  let F := ArithmeticFunction.vonMangoldt
  let M₀ := arithmeticLowCutoff U M
  let M₁ := arithmeticHighCutoff U M
  let F₀ := arithmeticLowCutoff V F
  let F₁ := arithmeticHighCutoff V F
  have hM : M₀ + M₁ = M := arithmeticLowCutoff_add_highCutoff U M
  have hF : F₀ + F₁ = F := arithmeticLowCutoff_add_highCutoff V F
  have hMZ : M * Z = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  have hFZ : F * Z = ArithmeticFunction.log := ArithmeticFunction.vonMangoldt_mul_zeta
  have hM₁Z : M₁ * Z = 1 - M₀ * Z := by
    calc
      _ = (M₀ + M₁) * Z - M₀ * Z := by ring
      _ = _ := by rw [hM, hMZ]
  have hcross : M₁ * (F₀ * Z) = F₀ - (M₀ * F₀) * Z := by
    calc
      _ = (M₁ * Z) * F₀ := by ring
      _ = _ := by rw [hM₁Z]; ring
  change F = M₀ * ArithmeticFunction.log + F₀ - (M₀ * F₀) * Z + M₁ * (F₁ * Z)
  calc
    F = M * (F * Z) := by rw [hFZ]; exact ArithmeticFunction.moebius_mul_log_eq_vonMangoldt.symm
    _ = M₀ * (F * Z) + M₁ * (F * Z) := by rw [← add_mul, hM]
    _ = M₀ * ArithmeticFunction.log + (M₁ * (F₀ * Z) + M₁ * (F₁ * Z)) := by
      congr 1
      · rw [hFZ]
      · rw [← hF]; ring
    _ = _ := by rw [hcross]; ring

theorem vaughanTypeICoefficient_eq_zero_of_cutoff_lt {U V n : ℕ} (hn : U * V < n) :
    vaughanTypeICoefficient U V n = 0 := by
  rw [vaughanTypeICoefficient, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro x hx
  by_cases h₁ : x.1 ≤ U
  · have h₂ : ¬ x.2 ≤ V := by
      intro h₂
      apply (not_le_of_gt hn)
      rw [← (Nat.mem_divisorsAntidiagonal.mp hx).1]
      exact Nat.mul_le_mul h₁ h₂
    simp [arithmeticLowCutoff_apply, h₂]
  · simp [arithmeticLowCutoff_apply, h₁]

/-- The first convolution coefficient has logarithmic absolute size. -/
theorem abs_vaughanTypeICoefficient_le_log (U V n : ℕ) :
    |vaughanTypeICoefficient U V n| ≤ Real.log (n : ℝ) := by
  rw [vaughanTypeICoefficient, ArithmeticFunction.mul_apply]
  calc
    _ ≤ ∑ x ∈ n.divisorsAntidiagonal,
        |arithmeticLowCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ) x.1 *
          arithmeticLowCutoff V ArithmeticFunction.vonMangoldt x.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ n.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt x.2 := by
      apply Finset.sum_le_sum
      intro x _
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := x.2)
      by_cases h₁ : x.1 ≤ U
      · by_cases h₂ : x.2 ≤ V
        · have hM : |((ArithmeticFunction.moebius x.1 : ℤ) : ℝ)| ≤ 1 := by
            exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := x.1))
          simp only [arithmeticLowCutoff_apply, if_pos h₁, if_pos h₂,
            ArithmeticFunction.intCoe_apply, abs_mul, abs_of_nonneg hΛ]
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hM hΛ
        · simpa only [arithmeticLowCutoff_apply, if_neg h₂, mul_zero, abs_zero] using hΛ
      · simpa only [arithmeticLowCutoff_apply, if_neg h₁, zero_mul, abs_zero] using hΛ
    _ = _ := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ j => ArithmeticFunction.vonMangoldt j),
        ArithmeticFunction.vonMangoldt_sum]

theorem vaughanTypeIIRight_eq_zero_of_le_cutoff {V n : ℕ} (hn : n ≤ V) :
    vaughanTypeIIRight V n = 0 := by
  rw [vaughanTypeIIRight, ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro m hm
  have hdiv := Nat.mem_divisors.mp hm
  have hmV : m ≤ V := (Nat.le_of_dvd (Nat.pos_of_ne_zero hdiv.2) hdiv.1).trans hn
  simp [arithmeticHighCutoff_apply, not_lt_of_ge hmV]

/-- The second Type II coefficient is nonnegative and at most logarithmic. -/
theorem vaughanTypeIIRight_bounds (V n : ℕ) :
    0 ≤ vaughanTypeIIRight V n ∧ vaughanTypeIIRight V n ≤ Real.log (n : ℝ) := by
  rw [vaughanTypeIIRight, ArithmeticFunction.coe_mul_zeta_apply,
    ← ArithmeticFunction.vonMangoldt_sum]
  have hbound (m : ℕ) :
      0 ≤ arithmeticHighCutoff V ArithmeticFunction.vonMangoldt m ∧
        arithmeticHighCutoff V ArithmeticFunction.vonMangoldt m ≤
          ArithmeticFunction.vonMangoldt m := by
    by_cases hm : V < m <;>
      simp [arithmeticHighCutoff_apply, hm, ArithmeticFunction.vonMangoldt_nonneg]
  exact ⟨Finset.sum_nonneg fun m _ => (hbound m).1, Finset.sum_le_sum fun m _ => (hbound m).2⟩

/-- Expand a weighted convolution sum into a bilinear sum with the original
cutoff on the product retained exactly. -/
theorem sum_map_convolution_eq_bilinear {R S : Type*} [Semiring R] [Semiring S]
    (j : R →+* S)
    (X : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Ioc 0 X)
    (f g : ArithmeticFunction R) (F : ℕ → S) :
    (∑ n ∈ A, j ((f * g) n) * F n) =
      ∑ d ∈ Finset.Ioc 0 X, ∑ m ∈ Finset.Ioc 0 X,
        if d * m ∈ A then j (f d) * j (g m) * F (d * m) else 0 := by
  let B := Finset.Ioc 0 X
  let P := (B ×ˢ B).filter (fun a : ℕ × ℕ => a.1 * a.2 ∈ A)
  let val (a : ℕ × ℕ) := a.1 * a.2
  let term (a : ℕ × ℕ) := j (f a.1) * j (g a.2) * F (val a)
  have he : (∑ a ∈ P, term a) =
      ∑ d ∈ B, ∑ m ∈ B, if d * m ∈ A then j (f d) * j (g m) * F (d * m) else 0 := by
    simp only [P, Finset.sum_filter, Finset.sum_product, term, val]
  rw [← he]
  have hmap : ∀ a ∈ P, val a ∈ A := fun _ ha => (Finset.mem_filter.mp ha).2
  rw [← Finset.sum_fiberwise_of_maps_to hmap term]
  apply Finset.sum_congr rfl
  intro n hn
  have hpos := (Finset.mem_Ioc.mp (hA hn)).1
  have hle := (Finset.mem_Ioc.mp (hA hn)).2
  have hset : P.filter (fun a => val a = n) = n.divisorsAntidiagonal := by
    ext a
    simp only [P, val, Finset.mem_filter, Finset.mem_product, B, Finset.mem_Ioc,
      Nat.mem_divisorsAntidiagonal]
    constructor
    · intro ha
      exact ⟨ha.2, hpos.ne'⟩
    · rintro ⟨hprod, hn₀⟩
      have ha : 0 < a.1 * a.2 := hprod.symm ▸ hpos
      have ha₁ : 0 < a.1 := Nat.pos_of_ne_zero (fun h => by simpa [h] using ha)
      have ha₂ : 0 < a.2 := Nat.pos_of_ne_zero (fun h => by simpa [h] using ha)
      have h₁ : a.1 ≤ n := hprod ▸ Nat.le_mul_of_pos_right _ ha₂
      have h₂ : a.2 ≤ n := hprod ▸ Nat.le_mul_of_pos_left _ ha₁
      exact ⟨⟨⟨⟨ha₁, h₁.trans hle⟩, ha₂, h₂.trans hle⟩, hprod.symm ▸ hn⟩, hprod⟩
  rw [ArithmeticFunction.mul_apply, map_sum, Finset.sum_mul, hset]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [term, val, (Nat.mem_divisorsAntidiagonal.mp ha).1, map_mul]

/-- Expand convolution against a test over a subset of the positive interval. -/
theorem sum_convolution_eq_bilinear {R : Type*} [Semiring R]
    (X : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Ioc 0 X)
    (f g : ArithmeticFunction R) (F : ℕ → R) :
    (∑ n ∈ A, (f * g) n * F n) =
      ∑ d ∈ Finset.Ioc 0 X, ∑ m ∈ Finset.Ioc 0 X,
        if d * m ∈ A then f d * g m * F (d * m) else 0 :=
  sum_map_convolution_eq_bilinear (RingHom.id R) X A hA f g F

end PrimeUniformity
