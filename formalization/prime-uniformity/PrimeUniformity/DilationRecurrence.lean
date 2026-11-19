module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Prod
public import PrimeUniformity.PhaseDetection
public import PrimeUniformity.PolynomialRecurrence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open scoped Classical BigOperators Polynomial

/-- A dense set of pairs has a fiber of at least the same relative density. -/
theorem exists_dense_product_fiber {A B : Type*} (s : Finset A) (t : Finset B)
    (hs : s.Nonempty) (G : A → B → Prop) (ρ : ℝ)
    (h : ρ * (s.card : ℝ) * (t.card : ℝ) ≤
      (((s ×ˢ t).filter (fun p : A × B => G p.1 p.2)).card : ℝ)) :
    ∃ i ∈ s, ρ * (t.card : ℝ) ≤ ((t.filter (G i)).card : ℝ) := by
  classical
  let U := (s ×ˢ t).filter (fun p => G p.1 p.2)
  have hmaps : ∀ p ∈ U, p.1 ∈ s := by
    intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hcard : s.card • (ρ * (t.card : ℝ)) ≤ (U.card : ℝ) := by
    rw [nsmul_eq_mul]
    convert h using 1
    ring
  obtain ⟨i, his, hi⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps hs hcard
  refine ⟨i, his, hi.trans ?_⟩
  exact_mod_cast Finset.card_le_card_of_injOn Prod.snd
    (s := U.filter (fun p => p.1 = i)) (t := t.filter (G i))
    (by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hU := Finset.mem_filter.mp hp'.1
      exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hU.1).2, hp'.2 ▸ hU.2⟩)
    (by
      intro p hp q hq h
      exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) h)

/-- For the separable phase that occurs in Type II, one-variable recovery
with an arbitrary constant term suffices to recover both coefficients.
The two denominators are combined with an explicit loss. -/
theorem recover_separable_dilation_coefficients
    (s t : Finset ℕ) (hs : s.Nonempty) (ht : t.Nonempty)
    (k D : ℕ) (ρ ε α β Eα Eβ : ℝ)
    (h : ρ * (s.card : ℝ) * (t.card : ℝ) ≤
      (((s ×ˢ t).filter (fun p : ℕ × ℕ => ∃ m : ℤ,
        |α * (p.1 : ℝ) ^ k + β * (p.2 : ℝ) ^ k - m| ≤ ε)).card : ℝ))
    (recoverS : ∀ c : ℝ, ρ * (s.card : ℝ) ≤
      ((s.filter (fun i : ℕ => ∃ m : ℤ, |α * (i : ℝ) ^ k + c - m| ≤ ε)).card : ℝ) →
      ∃ q : ℕ, 0 < q ∧ q ≤ D ∧ ∃ m : ℤ, |(q : ℝ) * α - m| ≤ Eα)
    (recoverT : ∀ c : ℝ, ρ * (t.card : ℝ) ≤
      ((t.filter (fun j : ℕ => ∃ m : ℤ, |β * (j : ℝ) ^ k + c - m| ≤ ε)).card : ℝ) →
      ∃ q : ℕ, 0 < q ∧ q ≤ D ∧ ∃ m : ℤ, |(q : ℝ) * β - m| ≤ Eβ) :
    ∃ q : ℕ, 0 < q ∧ q ≤ D ^ 2 ∧ ∃ a b : ℤ,
      |(q : ℝ) * α - a| ≤ (D : ℝ) * Eα ∧
      |(q : ℝ) * β - b| ≤ (D : ℝ) * Eβ := by
  classical
  let G (i j : ℕ) : Prop := ∃ m : ℤ, |α * (i : ℝ) ^ k + β * (j : ℝ) ^ k - m| ≤ ε
  obtain ⟨i, _, hi⟩ := exists_dense_product_fiber s t hs G ρ h
  have hswap : (((s ×ˢ t).filter (fun p => G p.1 p.2)).card) =
      (((t ×ˢ s).filter (fun p => G p.2 p.1)).card) := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
    · intro p hp
      simpa [and_left_comm, and_assoc] using hp
    · intro p _ r _ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro p hp
      exact ⟨(p.2, p.1), by simpa [and_left_comm, and_assoc] using hp, rfl⟩
  have ht' : ρ * (t.card : ℝ) * (s.card : ℝ) ≤
      (((t ×ˢ s).filter (fun p => G p.2 p.1)).card : ℝ) := by
    rw [← hswap]
    convert h using 1
    ring
  obtain ⟨j, _, hj⟩ := exists_dense_product_fiber t s ht (fun j i => G i j) ρ ht'
  obtain ⟨qα, hα, hαD, a, ha⟩ := recoverS (β * (j : ℝ) ^ k) hj
  obtain ⟨qβ, hβ, hβD, b, hb⟩ := recoverT (α * (i : ℝ) ^ k)
    (by simpa only [G, add_comm (α * (i : ℝ) ^ k)] using hi)
  refine ⟨qα * qβ, Nat.mul_pos hα hβ, by simpa only [pow_two] using Nat.mul_le_mul hαD hβD,
    (qβ : ℤ) * a, (qα : ℤ) * b, ?_, ?_⟩
  · have he : (((qα * qβ : ℕ) : ℝ) * α - (((qβ : ℤ) * a : ℤ) : ℝ)) =
        (qβ : ℝ) * ((qα : ℝ) * α - (a : ℝ)) := by push_cast; ring
    rw [he, abs_mul, abs_of_nonneg (Nat.cast_nonneg qβ)]
    exact mul_le_mul (by exact_mod_cast hβD) ha (abs_nonneg _) (Nat.cast_nonneg D)
  · have he : (((qα * qβ : ℕ) : ℝ) * β - (((qα : ℤ) * b : ℤ) : ℝ)) =
        (qα : ℝ) * ((qβ : ℝ) * β - (b : ℝ)) := by push_cast; ring
    rw [he, abs_mul, abs_of_nonneg (Nat.cast_nonneg qα)]
    exact mul_le_mul (by exact_mod_cast hαD) hb (abs_nonneg _) (Nat.cast_nonneg D)

/-- The ordinary monomial phase inverse needed for the two-variable recurrence.
The phase may include any real constant term. -/
def MonomialPhaseInverse (T : Finset ℕ) (k D : ℕ) (ρ A N : ℝ) : Prop :=
  ∀ θ c : ℝ, ρ / 16 ≤ ‖𝔼 n ∈ T, recurrencePhase (θ * (n : ℝ) ^ k + c)‖ →
    ∃ q : ℕ, 0 < q ∧ q ≤ D ∧ ∃ a : ℤ, |(q : ℝ) * θ - a| ≤ A / N ^ k

/-- Fourier detection and interpolation give a sharp coefficient estimate
from any ordinary monomial phase inverse at the indicated frequency budget. -/
theorem recover_monomial_of_near_integers
    (T S : Finset ℕ) (hT : T.Nonempty) (hST : S ⊆ T)
    {k R D r B : ℕ} {ρ ε A N α b : ℝ}
    (hk : 0 < k) (hR : 0 < R) (hr : 0 < r) (hN : 0 < N)
    (hρ : 0 < ρ) (hε : 0 ≤ ε) (hB : A + 1 ≤ (B : ℝ))
    (hRρ : 16 ≤ ρ * R) (hsmall : 2 * Real.pi * R * ε ≤ 1 / 2)
    (hεRD : ((R * D : ℕ) : ℝ) * ε ≤ 1)
    (hsize : ((2 * B + 3) * (k * r + 1) : ℕ) ≤ S.card)
    (hdense : ρ * (T.card : ℝ) ≤ S.card)
    (hinterval : ∀ n ∈ S, (n : ℝ) ∈ Set.Icc 0 N)
    (hnear : ∀ n ∈ S, ∃ z : ℤ, |α * (n : ℝ) ^ k + b - z| ≤ ε)
    (hinverse : MonomialPhaseInverse T k D ρ A N) :
    ∃ q : ℕ, 0 < q ∧ q ≤ R * D ∧ ∃ a : ℤ,
      |(q : ℝ) * α - a| ≤ interpolationCoefficientConstant k *
        ((k + 1 : ℕ) * (N / (r : ℝ)) ^ k * (((R * D : ℕ) : ℝ) * ε)) / N ^ k := by
  obtain ⟨m, hm, hmR, hphase⟩ :=
    large_positive_phase_average_of_near_integers T S hT hST R hR ρ ε hρ hε hRρ hsmall hdense
      (fun n => α * (n : ℝ) ^ k + b) hnear
  have he (n : ℕ) : (m : ℝ) * (α * (n : ℝ) ^ k + b) =
      ((m : ℝ) * α) * (n : ℝ) ^ k + (m : ℝ) * b := by ring
  obtain ⟨q, hq, hqD, a, ha⟩ := hinverse ((m : ℝ) * α) ((m : ℝ) * b)
    (by simpa only [he] using hphase)
  have hmq : m * q ≤ R * D := Nat.mul_le_mul hmR.le hqD
  have hbudget : ((m * q : ℕ) : ℝ) * ε ≤ ((R * D : ℕ) : ℝ) * ε :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hmq) hε
  have hcoarse : |((m * q : ℕ) : ℝ) * α - a| ≤ A / N ^ k := by
    simpa only [Nat.cast_mul, mul_left_comm, ← mul_assoc, mul_comm (m : ℝ) (q : ℝ)] using ha
  let emb : ℕ ↪ ℤ := ⟨fun x => (x : ℤ), Int.ofNat_injective⟩
  have hsharp := sharpen_monomial_dilation_approximation hk (Nat.mul_pos hm hq) hr hN hε
    (hbudget.trans hεRD) a hcoarse hB (S.map emb)
    (by simpa only [Finset.card_map] using hsize)
    (fun n hn => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hn
      simpa only [emb, Function.Embedding.coeFn_mk, Int.cast_natCast] using hinterval x hx)
    (fun n hn => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hn
      simpa only [emb, Function.Embedding.coeFn_mk, Int.cast_natCast] using hnear x hx)
  refine ⟨m * q, Nat.mul_pos hm hq, hmq, a, hsharp.trans ?_⟩
  have hC : 0 ≤ interpolationCoefficientConstant k := by
    unfold interpolationCoefficientConstant
    exact add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _)
  gcongr

/-- For the separable phase in Type II, two ordinary one-variable inverses
suffice for sharp approximation with a common denominator. -/
theorem recover_separable_dilation_from_phase_inverse
    (T : Finset ℕ) (hT : T.Nonempty) {k R D r B : ℕ} {ρ ε A N α β : ℝ}
    (hk : 0 < k) (hR : 0 < R) (hr : 0 < r) (hN : 0 < N)
    (hρ : 0 < ρ) (hε : 0 ≤ ε) (hB : A + 1 ≤ (B : ℝ))
    (hRρ : 16 ≤ ρ * R) (hsmall : 2 * Real.pi * R * ε ≤ 1 / 2)
    (hεRD : ((R * D : ℕ) : ℝ) * ε ≤ 1)
    (hsize : (((2 * B + 3) * (k * r + 1) : ℕ) : ℝ) ≤ ρ * (T.card : ℝ))
    (hinterval : ∀ n ∈ T, (n : ℝ) ∈ Set.Icc 0 N)
    (hdense : ρ * (T.card : ℝ) * (T.card : ℝ) ≤
      (((T ×ˢ T).filter (fun p : ℕ × ℕ => ∃ z : ℤ,
        |α * (p.1 : ℝ) ^ k + β * (p.2 : ℝ) ^ k - z| ≤ ε)).card : ℝ))
    (hinverse : MonomialPhaseInverse T k D ρ A N) :
    let E := ((R * D : ℕ) : ℝ) * (interpolationCoefficientConstant k *
      ((k + 1 : ℕ) * (N / (r : ℝ)) ^ k * (((R * D : ℕ) : ℝ) * ε)) / N ^ k)
    ∃ q : ℕ, 0 < q ∧ q ≤ (R * D) ^ 2 ∧ ∃ a b : ℤ,
      |(q : ℝ) * α - a| ≤ E ∧ |(q : ℝ) * β - b| ≤ E := by
  have hrecover (θ c : ℝ)
      (hd : ρ * (T.card : ℝ) ≤
        ((T.filter (fun n : ℕ => ∃ z : ℤ, |θ * (n : ℝ) ^ k + c - z| ≤ ε)).card : ℝ)) := by
    let S := T.filter (fun n : ℕ => ∃ z : ℤ, |θ * (n : ℝ) ^ k + c - z| ≤ ε)
    exact recover_monomial_of_near_integers T S hT (Finset.filter_subset _ _)
      hk hR hr hN hρ hε hB hRρ hsmall hεRD
      (by simpa only [Nat.cast_le] using hsize.trans hd) hd
      (fun n hn => hinterval n (Finset.mem_filter.mp hn).1)
      (fun n hn => (Finset.mem_filter.mp hn).2) hinverse
  exact recover_separable_dilation_coefficients T T hT hT k (R * D) ρ ε α β _ _ hdense
    (hrecover α) (hrecover β)

/-- Choose the interpolation spacing from the lower bound for the number of
near-integer points. The factor four accommodates the integer rounding. -/
theorem exists_dilation_interpolation_spacing (k B : ℕ) {M : ℝ}
    (hM : 4 * (2 * (B : ℝ) + 3) * (k + 1) ≤ M) :
    ∃ r : ℕ, 0 < r ∧ (((2 * B + 3) * (k * r + 1) : ℕ) : ℝ) ≤ M ∧
      M / (4 * (2 * (B : ℝ) + 3) * (k + 1)) ≤ r := by
  let W := (2 * (B : ℝ) + 3) * (k + 1)
  have hW : 0 < W := by dsimp [W]; positivity
  have h4W : 4 * W ≤ M := by rw [show 4 * W = 4 * (2 * (B : ℝ) + 3) * (k + 1) by dsimp [W]; ring]; exact hM
  let x := M / (2 * W)
  have hx : 2 ≤ x := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * W)).mpr
    linarith
  let r := ⌊x⌋₊
  have hrle : (r : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxlt : x < (r : ℝ) + 1 := Nat.lt_floor_add_one x
  have hr : 0 < r := Nat.cast_pos.mp (by linarith : (0 : ℝ) < r)
  have hrone : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr.ne'
  have hhalf : x / 2 ≤ (r : ℝ) := by linarith
  refine ⟨r, hr, ?_, ?_⟩
  · push_cast
    calc
      (2 * (B : ℝ) + 3) * ((k : ℝ) * r + 1) ≤ (2 * (B : ℝ) + 3) * ((k + 1) * r) := by
        gcongr
        linarith
      _ = W * r := by dsimp [W]; ring
      _ ≤ W * x := mul_le_mul_of_nonneg_left hrle hW.le
      _ = M / 2 := by dsimp [x]; field_simp
      _ ≤ M := by linarith
  · calc
      _ = x / 2 := by dsimp [x, W]; field_simp; ring
      _ ≤ _ := hhalf

/-- The monomial coefficient in a sum of two dilated polynomials separates
into the original two coefficients multiplied by the relevant powers. -/
theorem coeff_pair_dilation (p₀ p₁ : ℝ[X]) (u v : ℝ) (j : ℕ) :
    (p₀.comp (Polynomial.C u * Polynomial.X) +
      p₁.comp (Polynomial.C v * Polynomial.X)).coeff j =
      p₀.coeff j * u ^ j + p₁.coeff j * v ^ j := by
  simp only [Polynomial.coeff_add, Polynomial.comp_C_mul_X_coeff]

/-- With dense dilation parameters at scale `L` and recurrence error at
scale `X / L`, interpolation gives coefficient error at scale `X`. -/
theorem recover_pair_dilation_at_ambient_scale
    (T : Finset ℕ) (hT : T.Nonempty)
    (p₀ p₁ : ℝ[X]) {k R D B : ℕ} {ρ H A L X c : ℝ}
    (hk : 0 < k) (hR : 0 < R) (hL : 0 < L) (hX : 0 < X)
    (hρ : 0 < ρ) (hH : 0 ≤ H) (hc : 0 < c)
    (hB : A + 1 ≤ (B : ℝ)) (hRρ : 16 ≤ ρ * R)
    (hsmall : 2 * Real.pi * R * (H / (X / L) ^ k) ≤ 1 / 2)
    (hεRD : ((R * D : ℕ) : ℝ) * (H / (X / L) ^ k) ≤ 1)
    (hsize : 4 * (2 * (B : ℝ) + 3) * (k + 1) ≤ ρ * (T.card : ℝ))
    (hcard : L ≤ c * (T.card : ℝ))
    (hinterval : ∀ n ∈ T, (n : ℝ) ∈ Set.Icc 0 L)
    (hdense : ρ * (T.card : ℝ) * (T.card : ℝ) ≤
      (((T ×ˢ T).filter (fun p : ℕ × ℕ => ∃ z : ℤ,
        |(p₀.comp (Polynomial.C (p.1 : ℝ) * Polynomial.X) +
          p₁.comp (Polynomial.C (p.2 : ℝ) * Polynomial.X)).coeff k - z| ≤
          H / (X / L) ^ k)).card : ℝ))
    (hinverse : MonomialPhaseInverse T k D ρ A L) :
    let K := 4 * (2 * (B : ℝ) + 3) * (k + 1) * c / ρ
    let E := ((R * D : ℕ) : ℝ) ^ 2 * interpolationCoefficientConstant k *
      (k + 1) * K ^ k * H / X ^ k
    ∃ q : ℕ, 0 < q ∧ q ≤ (R * D) ^ 2 ∧ ∃ a b : ℤ,
      |(q : ℝ) * p₀.coeff k - a| ≤ E ∧ |(q : ℝ) * p₁.coeff k - b| ≤ E := by
  dsimp
  obtain ⟨r, hr, hrsize, hrbound⟩ := exists_dilation_interpolation_spacing k B hsize
  have hε : 0 ≤ H / (X / L) ^ k := div_nonneg hH (by positivity)
  obtain ⟨q, hq, hqD, a, b, ha, hb⟩ :=
    recover_separable_dilation_from_phase_inverse T hT hk hR hr hL hρ hε hB hRρ hsmall
      hεRD hrsize hinterval (by simpa only [coeff_pair_dilation] using hdense) hinverse
  let K := 4 * (2 * (B : ℝ) + 3) * (k + 1) * c / ρ
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hW : 0 < 4 * (2 * (B : ℝ) + 3) * (k + 1) := by positivity
  have hratio : L / (r : ℝ) ≤ K := by
    apply (div_le_iff₀ hrR).mpr
    have hr' := (div_le_iff₀ hW).mp hrbound
    dsimp [K]
    rw [div_mul_eq_mul_div, le_div_iff₀ hρ]
    calc
      L * ρ = ρ * L := mul_comm _ _
      _ ≤ ρ * (c * (T.card : ℝ)) := mul_le_mul_of_nonneg_left hcard hρ.le
      _ = (ρ * (T.card : ℝ)) * c := by ring
      _ ≤ ((r : ℝ) * (4 * (2 * (B : ℝ) + 3) * (k + 1))) * c :=
        mul_le_mul_of_nonneg_right hr' hc.le
      _ = _ := by ring
  have hC : 0 ≤ interpolationCoefficientConstant k := by
    unfold interpolationCoefficientConstant
    exact add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have herror : ((R * D : ℕ) : ℝ) *
      (interpolationCoefficientConstant k *
        ((k + 1 : ℕ) * (L / (r : ℝ)) ^ k * (((R * D : ℕ) : ℝ) * (H / (X / L) ^ k))) /
          L ^ k) ≤
      ((R * D : ℕ) : ℝ) ^ 2 * interpolationCoefficientConstant k *
        (k + 1) * K ^ k * H / X ^ k := by
    push_cast
    calc
      _ = ((R : ℝ) * D) ^ 2 * interpolationCoefficientConstant k *
          ((k : ℝ) + 1) * (L / (r : ℝ)) ^ k * H / X ^ k := by
        simp only [← mul_div_assoc]
        rw [div_div, ← mul_pow, div_mul_cancel₀ _ hL.ne']
        ring
      _ ≤ _ := by gcongr
  exact ⟨q, hq, hqD, a, b, ha.trans herror, hb.trans herror⟩

/-- Clear the denominators for a finite family of coefficient estimates.
For any one coefficient the error is multiplied only by the budgets for
the other coefficients. -/
theorem common_denominator_of_coefficient_estimates {ι : Type*} [Fintype ι]
    (θ E : ι → ℝ) (D : ι → ℕ)
    (h : ∀ i, ∃ q : ℕ, ∃ a : ℤ, 0 < q ∧ q ≤ D i ∧ |(q : ℝ) * θ i - a| ≤ E i) :
    ∃ Q : ℕ, 0 < Q ∧ Q ≤ (∏ i, D i) ∧ ∀ i, ∃ a : ℤ,
      |(Q : ℝ) * θ i - a| ≤ (((∏ j ∈ (Finset.univ.erase i), D j) : ℕ) : ℝ) * E i := by
  classical
  choose q a hq hqD ha using h
  have hQ : 0 < ∏ j : ι, q j := Finset.prod_pos (fun j _ => hq j)
  have hQD : (∏ j, q j) ≤ ∏ j, D j := by
    gcongr with j <;> exact hqD j
  refine ⟨∏ j, q j, hQ, hQD, ?_⟩
  intro i
  let M := ∏ j ∈ Finset.univ.erase i, q j
  have hM : M ≤ ∏ j ∈ Finset.univ.erase i, D j := by
    dsimp only [M]
    gcongr with j <;> exact hqD j
  refine ⟨(M : ℤ) * a i, ?_⟩
  have hprod : q i * M = ∏ j, q j := Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)
  rw [← hprod, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  have he : (q i : ℝ) * (M : ℝ) * θ i - (M : ℝ) * (a i : ℝ) =
      (M : ℝ) * ((q i : ℝ) * θ i - (a i : ℝ)) := by ring
  rw [he, abs_mul, abs_of_nonneg (Nat.cast_nonneg M)]
  exact mul_le_mul (by exact_mod_cast hM) (ha i) (abs_nonneg _) (by positivity)

end PrimeUniformity
