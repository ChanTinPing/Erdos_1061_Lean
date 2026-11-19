module

public import PrimeUniformity.ProgressionBoundary
public import PrimeUniformity.UpstreamInverseReduction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PrimeUniformity

open Filter BigOperators

/-- Conjugating the test preserves the absolute correlation against a real weight. -/
theorem intervalCorrelation_star (X : ℕ) (w : ℤ → ℝ) (F : ℤ → ℂ) :
    intervalCorrelation X w (fun n => star (F n)) = intervalCorrelation X w F := by
  simp only [intervalCorrelation, Finset.expect_eq_sum_div_card, norm_div, star_star]
  congr 1
  rw [← norm_star (∑ n ∈ Finset.Ico (1 : ℤ) (1 + (X : ℤ)), (w n : ℂ) * star (F n)), star_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [star_mul, star_star, mul_comm]
  exact congrArg ((F n * ·) : ℂ → ℂ) (Complex.conj_ofReal (w n)).symm

/-- A bounded test supported on one residue class is limited by its density
in the ambient averaging interval. -/
theorem intervalCorrelation_residue_le {X q : ℕ} (hq : 0 < q)
    (a : ZMod q) (w : ℤ → ℝ) (F : ℤ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ n ∈ interval 1 (X : ℤ), |w n| ≤ B)
    (hF : ∀ n ∈ interval 1 (X : ℤ), ‖F n‖ ≤ 1)
    (hsupport : ∀ n ∈ interval 1 (X : ℤ), (n : ZMod q) ≠ a → F n = 0) :
    intervalCorrelation X w F ≤ B / (q : ℝ) + B / (X : ℝ) := by
  by_cases hX : X = 0
  · simpa [hX, intervalCorrelation] using
      (div_nonneg hB (Nat.cast_nonneg q))
  have hXp : (0 : ℝ) < X := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hX)
  let I := interval 1 (X : ℤ)
  let P := residueSlice 1 (X : ℤ) a
  let f (n : ℤ) : ℂ := (w n : ℂ) * star (F n)
  have hcard : (I.card : ℂ) = (X : ℂ) := by
    exact_mod_cast (show (I.card : ℝ) = (X : ℝ) by
      simpa [I] using card_interval 1 (X : ℤ) (by positivity))
  have hsum : (∑ n ∈ P, f n) = ∑ n ∈ I, f n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hnP
    have ha : (n : ZMod q) ≠ a := fun h => hnP (Finset.mem_filter.mpr ⟨hn, h⟩)
    simp [f, hsupport n hn ha]
  have hnorm : ‖∑ n ∈ P, f n‖ ≤ (P.card : ℝ) * B := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _n ∈ P, B := by
        apply Finset.sum_le_sum
        intro n hn
        have hnI := (Finset.mem_filter.mp hn).1
        dsimp only [f]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_star]
        simpa only [mul_one] using mul_le_mul (hw n hnI) (hF n hnI) (norm_nonneg _) hB
      _ = _ := by simp [nsmul_eq_mul]
  change ‖𝔼 n ∈ I, f n‖ ≤ _
  rw [Finset.expect_eq_sum_div_card, hcard, norm_div, Complex.norm_natCast, ← hsum]
  calc
    _ ≤ (P.card : ℝ) * B / (X : ℝ) := div_le_div_of_nonneg_right hnorm hXp.le
    _ ≤ ((X : ℝ) / q + 1) * B / (X : ℝ) := by
      apply div_le_div_of_nonneg_right _ hXp.le
      apply mul_le_mul_of_nonneg_right _ hB
      simpa [P] using card_residueSlice_le 1 (X : ℤ) hq (by positivity) a
    _ = _ := by field_simp

/-- Reindex a progression-masked integer correlation into the natural
product support used in the Vaughan decomposition. -/
theorem intervalCorrelation_residue_mask {X U V q r : ℕ} (hUV : U ≤ V) (hVX : V ≤ X)
    (hr : r < q) (w : ℤ → ℝ) (F : ℤ → ℂ) :
    intervalCorrelation X w (fun n => if n ∈ residueSlice ((U : ℤ) + 1)
      ((V - U : ℕ) : ℤ) (r : ZMod q) then F n else 0) =
      ‖∑ n ∈ (Finset.Ioc U V).filter (fun n => n % q = r), (w (n : ℤ) : ℂ) * star (F n)‖ /
        (X : ℝ) := by
  let I := interval 1 (X : ℤ)
  let P := residueSlice ((U : ℤ) + 1) ((V - U : ℕ) : ℤ) (r : ZMod q)
  let A := (Finset.Ioc U V).filter (fun n => n % q = r)
  have hP (n : ℤ) : n ∈ P ↔ (U : ℤ) < n ∧ n ≤ (V : ℤ) ∧ (n : ZMod q) = (r : ZMod q) := by
    simp only [P, residueSlice, interval, Finset.mem_filter, Finset.mem_Ico, Int.natCast_sub hUV]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, hmod⟩
      exact ⟨by omega, by omega, hmod⟩
    · rintro ⟨h₁, h₂, hmod⟩
      exact ⟨⟨by omega, by omega⟩, hmod⟩
  have hsub : P ⊆ I := by
    intro n hn
    have hn' := (hP n).mp hn
    have hV : (V : ℤ) ≤ X := by exact_mod_cast hVX
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hmem (n : ℕ) : (n : ℤ) ∈ P ↔ n ∈ A := by
    rw [hP, Finset.mem_filter, Finset.mem_Ioc, Int.cast_natCast,
      ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hr]
    push_cast
    omega
  have himage : A.image (fun n : ℕ => (n : ℤ)) = P := by
    ext n
    refine ⟨?_, ?_⟩
    · rintro hn
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
      exact (hmem m).mpr hm
    · intro hn
      have hn₀ : 0 ≤ n := by have := (hP n).mp hn; omega
      have he := Int.toNat_of_nonneg hn₀
      exact Finset.mem_image.mpr ⟨n.toNat, (hmem _).mp (he.symm ▸ hn), he⟩
  have hsum :
      (∑ n ∈ I, (w n : ℂ) * star (if n ∈ P then F n else 0)) =
        ∑ n ∈ A, (w (n : ℤ) : ℂ) * star (F n) := by
    calc
      _ = ∑ n ∈ P, (w n : ℂ) * star (F n) := by
        symm
        refine (Finset.sum_congr rfl fun n hn => ?_).trans (Finset.sum_subset hsub ?_)
        · rw [if_pos hn]
        · intro n _ hn
          rw [if_neg hn, star_zero, mul_zero]
      _ = _ := by
        have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := fun _ _ h => Int.ofNat.inj h
        rw [← himage, Finset.sum_image hinj.injOn]
  have hcard : I.card = X := by exact_mod_cast (card_interval 1 (X : ℤ) (by positivity))
  change ‖𝔼 n ∈ I, (w n : ℂ) * star (if n ∈ P then F n else 0)‖ = _
  rw [Finset.expect_eq_sum_div_card, hsum, hcard, norm_div, Complex.norm_natCast]

/-- The arithmetic-progression endpoint of the prime correlation
argument. The bound extends to finite complex linear combinations with
the sum of coefficient norms as the only extra factor. -/
theorem uniform_prime_cramer_progression_tests (h : UniformPrimePrefixEstimate) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ {ι : Type} (s : Finset ι) (U V q : ι → ℕ) (a : ∀ i, ZMod (q i)) (z : ι → ℂ),
        (∀ i ∈ s, U i ≤ V i ∧ V i ≤ X ∧ 0 < q i) →
        intervalCorrelation X (strictVonMangoldtCramerDifference X)
          (fun n => ∑ i ∈ s, if n ∈ residueSlice ((U i : ℤ) + 1) ((V i - U i : ℕ) : ℤ) (a i)
            then z i else 0) ≤
          C * Real.exp (-c * Real.log (X : ℝ) ^ (1 / 20 : ℝ)) * ∑ i ∈ s, ‖z i‖ := by
  obtain ⟨c, C, hc, hC, hprog⟩ := uniform_prime_cramer_progressions h
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [hprog, eventually_gt_atTop (0 : ℕ)] with X hprog hX
  intro ι s U V q a z hparams
  let I := interval 1 (X : ℤ)
  let P (i : ι) := residueSlice ((U i : ℤ) + 1) ((V i - U i : ℕ) : ℤ) (a i)
  let w := strictVonMangoldtCramerDifference X
  let E := Real.exp (-c * Real.log (X : ℝ) ^ (1 / 20 : ℝ))
  have hsub (i : ι) (hi : i ∈ s) : P i ⊆ I := by
    intro n hn
    have ⟨hUV, hVX, _⟩ := hparams i hi
    have hP := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
    have hU : (U i : ℤ) ≤ V i := by exact_mod_cast hUV
    have hV : (V i : ℤ) ≤ X := by exact_mod_cast hVX
    change _ ≤ n ∧ n < _ at hP
    rw [Int.natCast_sub hUV] at hP
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hsum :
      (∑ n ∈ I, (w n : ℂ) * star (∑ i ∈ s, if n ∈ P i then z i else 0)) =
        ∑ i ∈ s, star (z i) * ((∑ n ∈ P i, w n : ℝ) : ℂ) := by
    simp only [star_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Complex.ofReal_sum, Finset.mul_sum]
    have hset : I.filter (· ∈ P i) = P i := by
      ext n
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun h => ⟨hsub i hi h, h⟩⟩
    conv_rhs => rw [← hset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n ∈ P i <;> simp [hn, mul_comm]
  change ‖𝔼 n ∈ I, (w n : ℂ) * star (∑ i ∈ s, if n ∈ P i then z i else 0)‖ ≤ _
  have hcard : (I.card : ℂ) = (X : ℂ) := by
    have hcard' : I.card = X := by
      exact_mod_cast (card_interval 1 (X : ℤ) (by positivity))
    rw [hcard']
  have hxr : 0 < (X : ℝ) := by exact_mod_cast hX
  rw [Finset.expect_eq_sum_div_card, hsum, hcard, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hxr).mpr
  calc
    _ ≤ ∑ i ∈ s, ‖star (z i) * ((∑ n ∈ P i, w n : ℝ) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖z i‖ * (C * (X : ℝ) * E) := by
      apply Finset.sum_le_sum
      intro i hi
      have ⟨hUV, hVX, hq⟩ := hparams i hi
      rw [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hprog (U i) (V i) hUV hVX (q i) hq (a i))
        (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end PrimeUniformity
