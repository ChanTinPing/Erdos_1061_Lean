module

public import Jsp000881.Rectangles
import all Jsp000881.Rectangles
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.FieldSimp

public section

namespace Jsp000881

open Filter Asymptotics
open scoped BigOperators Topology

/-- Required finite parameter sieve. Local admissibility is checked for each
of the planes at scale `z = k^7`. -/
def GoodParameterFamily : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ᶠ k : ℕ in atTop,
    ∃ I : Finset PlaneIndex, a * (k : ℝ) ^ 28 ≤ (I.card : ℝ) ∧
      (I.card : ℝ) ≤ b * (k : ℝ) ^ 28 ∧
      ∀ θ ∈ I, ParameterBox θ ((k : ℤ) ^ 7) ∧ LocallyAdmissible θ

/-- The prime input only concerns the six explicit forms and the rectangle of
height `2^k` at parameter scale `k^7`. The constant is uniform in the plane. -/
def UniformPrimeRectangleLowerBound : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∀ᶠ k : ℕ in atTop, ∀ θ : PlaneIndex,
    ParameterBox θ ((k : ℤ) ^ 7) → LocallyAdmissible θ →
      d * (4 : ℝ) ^ k / (k : ℝ) ^ 6 ≤ (primePoints θ ((2 : ℤ) ^ k)).card

private noncomputable def perimeterScale (k : ℕ) : ℝ :=
  3600000000 * (k : ℝ) ^ 21 * (4 : ℝ) ^ k

private theorem perimeterScale_eq (k : ℕ) :
    (3600000000 : ℝ) * (((k : ℤ) ^ 7 : ℤ) : ℝ) ^ 3 *
      (((2 : ℤ) ^ k : ℤ) : ℝ) ^ 2 = perimeterScale k := by
  push_cast
  have hp : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul] <;> norm_num
  rw [hp]
  unfold perimeterScale
  ring

theorem eventually_large_lattice_scales : ∀ᶠ k : ℕ in atTop,
    100 ≤ (k : ℤ) ^ 7 ∧ 3 ≤ (2 : ℤ) ^ k := by
  filter_upwards [eventually_ge_atTop (100 : ℕ)] with k hk
  have hk' : (100 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  constructor
  · exact (show (100 : ℤ) ≤ (100 : ℤ) ^ 7 by decide).trans
      (pow_le_pow_left₀ (by decide) hk' _)
  · exact_mod_cast (show 3 ≤ (2 : ℕ) ^ k from
      (show 3 ≤ k by omega).trans k.lt_two_pow_self.le)

private theorem perimeterScale_tendsto : Tendsto perimeterScale atTop atTop := by
  refine tendsto_atTop_mono' _ ?_
    (tendsto_pow_atTop_atTop_of_one_lt (r := (4 : ℝ)) (by norm_num))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hpoly : (1 : ℝ) ≤ 3600000000 * (k : ℝ) ^ 21 :=
    one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hk')
  exact le_mul_of_one_le_left (by positivity) hpoly

private theorem duplicate_error (c b : ℝ) (hc : 0 < c) (hb : 0 < b) :
    ∀ᶠ k : ℕ in atTop, b ^ 2 * (k : ℝ) ^ 56 ≤ c * (k : ℝ) ^ 22 * (4 : ℝ) ^ k := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 56 (r := (4 : ℝ)) (by norm_num)
  have hsmall := (tendsto_order.1 ht).2 (c / b ^ 2) (div_pos hc (sq_pos_of_pos hb))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hsmall] with k hk hsmall'
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hexp : (0 : ℝ) < (4 : ℝ) ^ k := by positivity
  change (k : ℝ) ^ 56 / (4 : ℝ) ^ k < c / b ^ 2 at hsmall'
  have h := (lt_div_iff₀ (sq_pos_of_pos hb)).mp hsmall'
  calc
    _ = ((k : ℝ) ^ 56 / (4 : ℝ) ^ k * b ^ 2) * (4 : ℝ) ^ k := by
      field_simp [hexp.ne'] <;> ring
    _ ≤ c * (4 : ℝ) ^ k := mul_le_mul_of_nonneg_right h.le hexp.le
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hc.le (one_le_pow₀ hk')) hexp.le

private theorem scale_superlinear {c : ℝ} (hc : 0 < c) (M : ℝ) :
    ∀ᶠ k : ℕ in atTop, M * perimeterScale k ≤ c * (k : ℝ) ^ 22 * (4 : ℝ) ^ k := by
  have hk := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (M * 3600000000 / c)
  filter_upwards [hk] with k h
  have hcoef := (div_le_iff₀ hc).mp h
  calc
    _ = (M * 3600000000) * (k : ℝ) ^ 21 * (4 : ℝ) ^ k := by unfold perimeterScale; ring
    _ ≤ ((k : ℝ) * c) * (k : ℝ) ^ 21 * (4 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (by positivity)) (by positivity)
    _ = _ := by ring

private theorem scale_count_lower_bound (hI : GoodParameterFamily)
    (hprime : UniformPrimeRectangleLowerBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      c * (k : ℝ) ^ 22 * (4 : ℝ) ^ k ≤ S (perimeterScale k) := by
  obtain ⟨a, b, ha, hb, hI⟩ := hI
  obtain ⟨d, hd, hprime⟩ := hprime
  let c := a * d / 2
  have hc : 0 < c := div_pos (mul_pos ha hd) (by norm_num)
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_large_lattice_scales, hI,
    hprime, duplicate_error c b hc hb] with k hk hscale hI hprime herr
  obtain ⟨I, hlo, hhi, hbox⟩ := hI
  let F := fun θ : PlaneIndex => primeTuplesOn θ ((2 : ℤ) ^ k)
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hper : (3600000000 : ℝ) * (((k : ℤ) ^ 7 : ℤ) : ℝ) ^ 3 *
      (((2 : ℤ) ^ k : ℤ) : ℝ) ^ 2 ≤ perimeterScale k := (perimeterScale_eq k).le
  have htotal := sum_plane_counts_le_S_add_sq I F (perimeterScale k) fun θ hθ s hs =>
    primeTupleOn_realized hscale.1 hscale.2 (hbox θ hθ).1 hs hper
  have hindividual (θ : PlaneIndex) (hi : θ ∈ I) :
      d * (4 : ℝ) ^ k / (k : ℝ) ^ 6 ≤ ((F θ).card : ℝ) := by
    change _ ≤ ((primeTuplesOn θ ((2 : ℤ) ^ k)).card : ℝ)
    rw [card_primeTuplesOn hscale.1 hscale.2 (hbox θ hi).1]
    exact hprime θ (hbox θ hi).1 (hbox θ hi).2
  have hsum : (a * d) * (k : ℝ) ^ 22 * (4 : ℝ) ^ k ≤ ∑ θ ∈ I, ((F θ).card : ℝ) := by
    calc
      _ = (a * (k : ℝ) ^ 28) * (d * (4 : ℝ) ^ k / (k : ℝ) ^ 6) := by
        field_simp [hkr.ne'] <;> ring
      _ ≤ (I.card : ℝ) * (d * (4 : ℝ) ^ k / (k : ℝ) ^ 6) :=
        mul_le_mul_of_nonneg_right hlo (by positivity)
      _ = ∑ _θ ∈ I, d * (4 : ℝ) ^ k / (k : ℝ) ^ 6 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hindividual
  have hsq : (I.card : ℝ) ^ 2 ≤ b ^ 2 * (k : ℝ) ^ 56 := by
    calc
      _ ≤ (b * (k : ℝ) ^ 28) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hhi _
      _ = _ := by ring
  have hmain : (a * d) * (k : ℝ) ^ 22 * (4 : ℝ) ^ k =
      2 * (c * (k : ℝ) ^ 22 * (4 : ℝ) ^ k) := by dsimp [c]; ring
  rw [hmain] at hsum
  linarith only [hsum, htotal, hsq, herr]

theorem not_linear_asymptotic_of_uniform_prime_rectangle
    (hI : GoodParameterFamily) (hprime : UniformPrimeRectangleLowerBound) :
    ¬ ∃ c : ℝ, 0 < c ∧ S ~[atTop] (fun x : ℝ => c * x) := by
  rintro ⟨c, hc, he⟩
  obtain ⟨u, hu, hlower⟩ := scale_count_lower_bound hI hprime
  have hx : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop 0
  have hne : ∀ᶠ x : ℝ in atTop, c * x ≠ 0 := hx.mono fun _ h => (mul_pos hc h).ne'
  have hlim := (isEquivalent_iff_tendsto_one hne).mp he
  have hup : ∀ᶠ x : ℝ in atTop, S x / (c * x) < 2 :=
    (tendsto_order.1 hlim).2 2 (by norm_num)
  obtain ⟨k, hxk, huk, hmk, hlk⟩ := ((perimeterScale_tendsto.eventually hx).and
    ((perimeterScale_tendsto.eventually hup).and
      ((scale_superlinear hu (2 * c)).and hlower))).exists
  have hlt := (div_lt_iff₀ (mul_pos hc hxk)).mp huk
  exact (not_lt_of_ge (hmk.trans hlk)) (by simpa only [mul_assoc] using hlt)

end Jsp000881
