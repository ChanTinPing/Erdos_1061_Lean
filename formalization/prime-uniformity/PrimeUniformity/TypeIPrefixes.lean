module

public import PrimeUniformity.TypeIIBlocks
public import PrimeUniformity.PrimeCorrelationBounds
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators

/-- The largest unweighted Type I correlation over prefixes of the
multiplicative fiber. -/
noncomputable def typeIPrefixMax (X d : ℕ) (A : Finset ℕ) (F : ℕ → ℂ) : ℝ :=
  (Finset.range (X / d + 1)).sup' ⟨0, by simp⟩
    (fun k => ‖divisorCorrelation (A.filter (· ≤ d * k)) F d‖)

theorem norm_divisorCorrelation_prefix_le_typeIPrefixMax {X d k : ℕ}
    (hk : k ≤ X / d) (A : Finset ℕ) (F : ℕ → ℂ) :
    ‖divisorCorrelation (A.filter (· ≤ d * k)) F d‖ ≤ typeIPrefixMax X d A F := by
  unfold typeIPrefixMax
  exact Finset.le_sup' (fun j : ℕ => ‖divisorCorrelation (A.filter (· ≤ d * j)) F d‖)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

theorem exists_typeIPrefixMax (X d : ℕ) (A : Finset ℕ) (F : ℕ → ℂ) :
    ∃ k ≤ X / d, typeIPrefixMax X d A F = ‖divisorCorrelation (A.filter (· ≤ d * k)) F d‖ := by
  obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (X / d + 1))
    (H := ⟨0, by simp⟩) (fun k => ‖divisorCorrelation (A.filter (· ≤ d * k)) F d‖)
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), he⟩

private theorem typeIPrefixMax_nonneg (X d : ℕ) (A : Finset ℕ) (F : ℕ → ℂ) :
    0 ≤ typeIPrefixMax X d A F :=
  (norm_nonneg _).trans (norm_divisorCorrelation_prefix_le_typeIPrefixMax (Nat.zero_le _) A F)

/-- A one-bounded test controls every fiber by the number of its multiples. -/
theorem typeIPrefixMax_le {X d : ℕ} (A : Finset ℕ) (hA : A ⊆ Finset.Ioc 0 X) (F : ℕ → ℂ)
    (hF : ∀ n ∈ A, ‖F n‖ ≤ 1) : typeIPrefixMax X d A F ≤ ((X / d : ℕ) : ℝ) := by
  obtain ⟨k, _, hk⟩ := exists_typeIPrefixMax X d A F
  rw [hk]
  let S := (A.filter (· ≤ d * k)).filter (d ∣ ·)
  change ‖∑ n ∈ S, F n‖ ≤ _
  have hsub : S ⊆ (Finset.Ioc 0 X).filter (d ∣ ·) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hn', hd⟩
    exact Finset.mem_filter.mpr ⟨hA (Finset.mem_filter.mp hn').1, hd⟩
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _n ∈ S, (1 : ℝ) :=
      Finset.sum_le_sum fun n hn => hF n (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    _ = (S.card : ℝ) := by simp
    _ ≤ _ := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (Nat.Ioc_filter_dvd_card_eq_div X d)

/-- One dyadic block contains a dense set of positive factors with large
unweighted prefix correlations. -/
def DenseTypeIPrefixes (X D : ℕ) (A : Finset ℕ) (F : ℕ → ℂ) (δ : ℝ) : Prop :=
  ∃ i ≤ Nat.log 2 D, let B := dyadicFactorBlock 0 D i
      let E := B.filter (fun d => (δ / 2) * ((X : ℝ) / 2 ^ i) ≤ typeIPrefixMax X d A F)
      (δ / 2) * (2 : ℝ) ^ i ≤ (E.card : ℝ) ∧
      ∀ d ∈ E, ∃ k ≤ X / d, (δ / 2) * ((X : ℝ) / 2 ^ i) ≤
        ‖divisorCorrelation (A.filter (· ≤ d * k)) F d‖

/-- A large total prefix budget gives a dyadic block with many large
unweighted prefixes. Each selected modulus can use its own endpoint. -/
theorem exists_dense_large_typeIPrefixes {X D : ℕ} (hX : 0 < X) (A : Finset ℕ)
    (hA : A ⊆ Finset.Ioc 0 X) (F : ℕ → ℂ) (hF : ∀ n ∈ A, ‖F n‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hlarge : ((Nat.log 2 D + 1 : ℕ) : ℝ) * (δ * X) <
      ∑ d ∈ Finset.Ioc 0 D, typeIPrefixMax X d A F) :
    DenseTypeIPrefixes X D A F δ := by
  obtain ⟨i, hi, hsum⟩ : ∃ i ∈ Finset.range (Nat.log 2 D + 1),
      δ * (X : ℝ) < ∑ d ∈ dyadicFactorBlock 0 D i, typeIPrefixMax X d A F := by
    by_contra! h
    apply (not_le_of_gt hlarge)
    rw [sum_eq_dyadicFactorBlocks 0 D]
    calc
      _ ≤ ∑ _i ∈ Finset.range (Nat.log 2 D + 1), δ * (X : ℝ) := Finset.sum_le_sum h
      _ = _ := by simp [nsmul_eq_mul]
  let B := dyadicFactorBlock 0 D i
  let b (d : ℕ) := typeIPrefixMax X d A F
  let H := (X : ℝ) / (2 : ℝ) ^ i
  let T := (δ / 2) * H
  have hH : 0 < H := div_pos (by exact_mod_cast hX) (by positivity)
  have hcard : (B.card : ℝ) ≤ (2 : ℝ) ^ i := by exact_mod_cast card_dyadicFactorBlock_le 0 D i
  have hb (d : ℕ) (hd : d ∈ B) : b d ≤ H := by
    have hd' : (2 : ℝ) ^ i ≤ (d : ℝ) := by exact_mod_cast (mem_dyadicFactorBlock.mp hd).2.2.1
    exact (typeIPrefixMax_le A hA F hF).trans
      (Nat.cast_div_le.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hd'))
  have hT : 0 ≤ T := mul_nonneg (by positivity) hH.le
  have hbn (d : ℕ) : 0 ≤ b d := typeIPrefixMax_nonneg X d A F
  have hbnorm (d : ℕ) : ‖b d‖ = b d := Real.norm_of_nonneg (hbn d)
  have hbound := norm_sum_mul_le_card_threshold B (fun _ => (1 : ℂ)) (fun d => (b d : ℂ))
    (W := 1) (M := H) (T := T) zero_le_one hT (by simp)
    (fun d hd => by simpa only [Complex.norm_real, hbnorm] using hb d hd)
  have hnonneg : 0 ≤ ∑ d ∈ B, b d := Finset.sum_nonneg fun d _ => hbn d
  simp only [one_mul, ← Complex.ofReal_sum, Complex.norm_real,
    Real.norm_of_nonneg hnonneg, hbnorm] at hbound
  let E := B.filter (fun d => T ≤ b d)
  have hbound' : δ * (X : ℝ) ≤ ((2 : ℝ) ^ i * (δ / 2) + (E.card : ℝ)) * H := by
    calc
      _ ≤ ∑ d ∈ B, b d := hsum.le
      _ ≤ (B.card : ℝ) * T + (E.card : ℝ) * H := hbound
      _ ≤ (2 : ℝ) ^ i * T + (E.card : ℝ) * H :=
        add_le_add (mul_le_mul_of_nonneg_right hcard hT) le_rfl
      _ = _ := by dsimp only [T]; ring
  have hXeq : (2 : ℝ) ^ i * H = (X : ℝ) := by
    dsimp [H]
    field_simp
  rw [← hXeq, ← mul_assoc] at hbound'
  have hcancel := (mul_le_mul_iff_left₀ hH).mp hbound'
  refine ⟨i, Nat.lt_succ_iff.mp (Finset.mem_range.mp hi), by linarith, ?_⟩
  intro d hd
  obtain ⟨k, hk, heq⟩ := exists_typeIPrefixMax X d A F
  exact ⟨k, hk, heq ▸ (Finset.mem_filter.mp hd).2⟩

/-- A large prime–Cramér correlation forces either dense Type I prefixes
or one large Type II block. Both thresholds and both arithmetic errors
are explicit. -/
theorem prime_cramer_large_correlation_cases {X U V Q D : ℕ} (hX : 0 < X)
    (hU : U ≤ D) (hUV : U * V ≤ D) (hD : D ≤ X)
    (A : Finset ℕ) (hA : A ⊆ Finset.Ioc 0 X) (F : ℕ → ℂ) (hF : ∀ n ∈ A, ‖F n‖ ≤ 1)
    {δ E : ℝ} (hδ : 0 ≤ δ)
    (hlarge :
      (3 * Real.log (X : ℝ) + cramerNormalization Q) *
          (((Nat.log 2 D + 1 : ℕ) : ℝ) * (δ * X)) +
        (V : ℝ) * Real.log (X : ℝ) + ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 2 * E +
        (∑ n ∈ Finset.Ioc 0 X, |cramerWeight Q n - cramerTruncatedWeight Q D n|) <
        ‖∑ n ∈ A, ((ArithmeticFunction.vonMangoldt n - cramerWeight Q n : ℝ) : ℂ) * F n‖) :
    DenseTypeIPrefixes X D A F δ ∨
      ∃ i ≤ Nat.log 2 X, ∃ j ≤ Nat.log 2 X, E < ‖vaughanTypeIIBlock X U V i j A F‖ := by
  let b (d : ℕ) := typeIPrefixMax X d A F
  by_cases hI : ((Nat.log 2 D + 1 : ℕ) : ℝ) * (δ * X) < ∑ d ∈ Finset.Ioc 0 D, b d
  · exact Or.inl (exists_dense_large_typeIPrefixes hX A hA F hF hδ hI)
  · apply Or.inr
    apply exists_large_vaughanTypeIIBlock
    by_contra! hII
    have hC : 0 ≤ 3 * Real.log (X : ℝ) + cramerNormalization Q :=
      add_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hX)))
        (cramerNormalization_positive Q).le
    have hnorm := norm_prime_cramer_correlation_le (Q := Q) hX hU hUV hD A hA F hF b (fun _ _ _ hk =>
      norm_divisorCorrelation_prefix_le_typeIPrefixMax hk A F)
    exact (not_le_of_gt hlarge) (hnorm.trans (add_le_add
      (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (le_of_not_gt hI) hC) le_rfl) hII)
      le_rfl))

end PrimeUniformity
