module

public import PrimeUniformity.DilationRecurrence
public import PrimeUniformity.NearLattice
public import PrimeUniformity.WeylAverages
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Adapted from openai/math, `OAI/Combinatorics/SumProduct/Alignment/WeylInverse01.lean`,
revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, under Apache-2.0.
The imports and namespace have been narrowed to the scalar recurrence proof.
-/

@[expose] public section

namespace PrimeUniformity

namespace WeylInverse
open scoped BigOperators ComplexConjugate Polynomial
open WeylAverages NearLattice
noncomputable section

theorem density_of_large_average {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f : ι → ℝ) (t : ℝ) (ht : 0 ≤ t) (hf : ∀ x ∈ S, f x ≤ 1)
    (havg : 2 * t ≤ 𝔼 x ∈ S, f x) :
    t * S.card ≤ ((S.filter (fun x => t ≤ f x)).card : ℝ) := by
  classical
  have h : (∑ x ∈ S, f x) ≤ ∑ x ∈ S, (t + if t ≤ f x then (1 : ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro x hx
    split_ifs with htx
    · linarith [hf x hx]
    · linarith
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_boole] at h
  rw [Finset.expect_eq_sum_div_card] at havg
  have hc : 0 < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hS)
  have havg' := (le_div_iff₀ hc).mp havg
  nlinarith

theorem exists_dense_fiber (S : Finset ℕ) (A : ℕ) (hA : 0 < A) (q : ℕ → ℕ)
    (hq : ∀ n ∈ S, q n ∈ Finset.Icc 1 A) :
    ∃ a ∈ Finset.Icc 1 A,
      (S.card : ℝ) / A ≤ ((S.filter (fun n => q n = a)).card : ℝ) := by
  have hs : (Finset.Icc 1 A).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hA⟩⟩
  have he : (𝔼 a ∈ Finset.Icc 1 A, ((S.filter (fun n => q n = a)).card : ℝ)) =
      (S.card : ℝ) / A := by
    rw [Finset.expect_eq_sum_div_card]
    have hsum : (∑ a ∈ Finset.Icc 1 A, ((S.filter (fun n => q n = a)).card : ℝ)) = S.card := by
      exact_mod_cast (Finset.card_eq_sum_card_fiberwise hq).symm
    rw [hsum]
    simp
  exact Finset.exists_le_of_le_expect hs he.ge

theorem exists_dense_derivatives {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (f : ℕ → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (hlarge : δ ≤ ‖mean N f‖) (hboundary : 4 * (H : ℝ) / N ≤ δ ^ 2 / 2) :
    ∃ b ∈ Finset.range H, ∃ S : Finset ℕ,
      (∀ a ∈ S, a < H) ∧ δ ^ 2 / 4 * H ≤ (S.card : ℝ) ∧
      (∀ a ∈ S, δ ^ 2 / 4 ≤ ‖mean N (derivative a b f)‖) := by
  classical
  have hv := van_der_corput hN hH f hf
  rw [Finset.expect_comm] at hv
  have havg : δ ^ 2 / 2 ≤
      𝔼 b ∈ Finset.range H, 𝔼 a ∈ Finset.range H, ‖mean N (derivative a b f)‖ := by
    nlinarith [norm_nonneg (mean N f)]
  have hs := Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hH)
  obtain ⟨b, hb, hbavg⟩ := Finset.exists_le_of_le_expect hs havg
  let t := δ ^ 2 / 4
  let S := (Finset.range H).filter (fun a => t ≤ ‖mean N (derivative a b f)‖)
  refine ⟨b, hb, S, ?_, ?_, ?_⟩
  · intro a ha
    exact Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  · have h := density_of_large_average (Finset.range H) hs
      (fun a => ‖mean N (derivative a b f)‖) t (by dsimp [t]; positivity)
      (fun a _ => norm_mean_le_one _ (norm_derivative_le_one a b f hf))
      (by dsimp [t]; linarith)
    simpa only [Finset.card_range] using h
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

/-- A finite budget for the leading-coefficient Weyl inverse at correlation
at least the reciprocal of a positive integer. -/
def leadingInverseBudget : ℕ → ℕ → ℕ
  | 0, _ => 1
  | 1, n => n + 1
  | d + 2, n =>
    let A := leadingInverseBudget (d + 1) (4 * n ^ 2)
    let M := 16 * n ^ 2
    let K := 4 * A * n ^ 2
    let T := M * (32 * K ^ 2 + 1) + 16 * K * A + 2 * M + 1
    let Q := 2 * K * A * (d + 2)
    let C := 32 * K ^ 2 * A * M
    Q + C + T ^ (d + 2) + 1

/-- At each fixed degree the explicit Weyl budget is a natural polynomial
in the reciprocal correlation parameter. -/
theorem leadingInverseBudget_polynomial (d : ℕ) :
    ∃ q : ℕ[X], ∀ n : ℕ, q.eval n = leadingInverseBudget d n := by
  induction d with
  | zero => exact ⟨Polynomial.C 1, by simp [leadingInverseBudget]⟩
  | succ d ih =>
    cases d with
    | zero => exact ⟨Polynomial.X + 1, by simp [leadingInverseBudget]⟩
    | succ d =>
      obtain ⟨p, hp⟩ := ih
      let x : ℕ[X] := Polynomial.X
      let A := p.comp (4 * x ^ 2)
      let M := 16 * x ^ 2
      let K := 4 * A * x ^ 2
      let T := M * (32 * K ^ 2 + 1) + 16 * K * A + 2 * M + 1
      let Q := 2 * K * A * Polynomial.C (d + 2)
      let C := 32 * K ^ 2 * A * M
      exact ⟨Q + C + T ^ (d + 2) + 1, fun n => by
        simp [T, Q, C, K, M, A, x, hp, leadingInverseBudget]⟩

theorem leadingInverseBudget_pos (d n : ℕ) : 0 < leadingInverseBudget d n := by
  cases d with
  | zero => simp [leadingInverseBudget]
  | succ d =>
    cases d with
    | zero => simp [leadingInverseBudget]
    | succ d => simp [leadingInverseBudget]

theorem leading_inverse_one (B : ℕ) (δ : ℝ) (hδ : 0 < δ) (hB : 1 ≤ (B : ℝ) * δ)
    (N : ℕ) (hN : 0 < N) (p : Polynomial ℝ) (hp : p.natDegree ≤ 1)
    (hlarge : δ ≤ ‖mean N (polynomialPhase p)‖) :
    ∃ q : ℕ, 0 < q ∧ q ≤ leadingInverseBudget 1 B ∧ ∃ m : ℤ,
      |(q : ℝ) * p.coeff 1 - m| ≤ (leadingInverseBudget 1 B : ℝ) / (N : ℝ) ^ 1 := by
  have hA : 1 / δ ≤ (B : ℝ) := (div_le_iff₀ hδ).mpr hB
  have he (x : ℕ) : p.eval (x : ℝ) = p.coeff 1 * x + p.coeff 0 := by
    rw [Polynomial.eval_eq_sum_range' (show p.natDegree < 2 by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, mul_one, pow_one]
    ring
  change δ ≤ ‖mean N (fun x => phase (p.eval (x : ℝ)))‖ at hlarge
  simp_rw [he] at hlarge
  obtain ⟨m, hm⟩ := linear_inverse hN (p.coeff 1) (p.coeff 0) δ hδ hlarge
  refine ⟨1, by omega, by simp [leadingInverseBudget], m, ?_⟩
  simp only [Nat.cast_one, one_mul, pow_one]
  apply hm.trans
  calc
    1 / (δ * N) = (1 / δ) / N := by ring
    _ ≤ (leadingInverseBudget 1 B : ℝ) / N := by
      gcongr
      exact hA.trans (by simp [leadingInverseBudget])

theorem leading_inverse_step_at_length (d : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (A K L N H : ℕ) (hA : 0 < A) (hK : 0 < K) (hN : 0 < N)
    (hH : 0 < H)
    (hboundary : 4 * (H : ℝ) / N ≤ δ ^ 2 / 2)
    (hdensity : (1 : ℝ) / K ≤ δ ^ 2 / (4 * A))
    (hHsize : 32 * K ^ 2 ≤ H)
    (hεsmall : (A : ℝ) / (N : ℝ) ^ d ≤ 1 / (16 * K))
    (hHL : (N : ℝ) ≤ (H : ℝ) * L)
    (hprev : ∀ p : Polynomial ℝ, p.natDegree ≤ d →
      δ ^ 2 / 4 ≤ ‖mean N (polynomialPhase p)‖ →
      ∃ q : ℕ, 0 < q ∧ q ≤ A ∧ ∃ m : ℤ,
        |(q : ℝ) * p.coeff d - m| ≤ (A : ℝ) / (N : ℝ) ^ d)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ d + 1)
    (hlarge : δ ≤ ‖mean N (polynomialPhase p)‖) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 2 * K * A * (d + 1) ∧ ∃ m : ℤ,
      |(q : ℝ) * p.coeff (d + 1) - m| ≤
        (16 * (K : ℝ) ^ 2 * A * L) / (N : ℝ) ^ (d + 1) := by
  classical
  obtain ⟨b, _, S, hSH, hScard, hSlarge⟩ := exists_dense_derivatives hN hH
    (polynomialPhase p) (fun x => by simp [polynomialPhase]) δ hδ hlarge hboundary
  have hall : ∀ a : ℕ, ∃ q : ℕ, ∃ m : ℤ, a ∈ S →
      0 < q ∧ q ≤ A ∧
      |(q : ℝ) * (polynomialDifference a b p).coeff d - m| ≤
        (A : ℝ) / (N : ℝ) ^ d := by
    intro a
    by_cases ha : a ∈ S
    · obtain ⟨q, hq, hqA, m, hm⟩ := hprev (polynomialDifference a b p)
        (polynomialDifference_degree a b p d hp)
        (by simpa only [polynomialPhase_difference] using hSlarge a ha)
      exact ⟨q, m, fun _ => ⟨hq, hqA, hm⟩⟩
    · exact ⟨1, 0, fun h => (ha h).elim⟩
  choose q m hqm using hall
  obtain ⟨a, ha, hafiber⟩ := exists_dense_fiber S A hA q
    (fun n hn => Finset.mem_Icc.mpr ⟨(hqm n hn).1, (hqm n hn).2.1⟩)
  have ha₀ : 0 < a := (Finset.mem_Icc.mp ha).1
  have haA : a ≤ A := (Finset.mem_Icc.mp ha).2
  let T := S.filter (fun n => q n = a)
  have hTK : (H : ℝ) / K ≤ (T.card : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_right hdensity (Nat.cast_nonneg H)
    have h₂ := div_le_div_of_nonneg_right hScard (Nat.cast_nonneg A)
    change (S.card : ℝ) / A ≤ (T.card : ℝ) at hafiber
    have he : δ ^ 2 / 4 * H / A = δ ^ 2 / (4 * A) * H := by ring
    rw [he] at h₂
    have he' : (1 : ℝ) / K * H = (H : ℝ) / K := by ring
    rw [he'] at h₁
    exact h₁.trans (h₂.trans hafiber)
  let α : ℝ := (a : ℝ) * (d + 1 : ℕ) * p.coeff (d + 1)
  obtain ⟨u, hu₀, huK, z, hz⟩ := vinogradov_inverse T H K hK hHsize
    α (-α * b) ((A : ℝ) / (N : ℝ) ^ d) (by positivity) hεsmall
    (fun n hn => hSH n (Finset.mem_filter.mp hn).1) hTK (by
      intro n hn
      obtain ⟨hnS, hnq⟩ := Finset.mem_filter.mp hn
      refine ⟨m n, ?_⟩
      have hm := (hqm n hnS).2.2
      rw [hnq, polynomialDifference_coeff n b p d hp] at hm
      have heq : α * n + (-α * b) - m n =
          (a : ℝ) * ((d + 1 : ℕ) * p.coeff (d + 1) * ((n : ℝ) - b)) - m n := by
        dsimp [α]
        ring
      rw [heq]
      exact hm)
  refine ⟨u * a * (d + 1), by positivity,
    Nat.mul_le_mul_right _ (Nat.mul_le_mul huK haA), z, ?_⟩
  have he : ((u * a * (d + 1) : ℕ) : ℝ) * p.coeff (d + 1) = α * u := by
    dsimp [α]
    push_cast
    ring
  rw [he]
  apply hz.trans
  have hN₀ : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hH₀ : 0 < (H : ℝ) := Nat.cast_pos.mpr hH
  have hi : (1 : ℝ) / H ≤ (L : ℝ) / N := by
    apply (div_le_div_iff₀ hH₀ hN₀).mpr
    nlinarith only [hHL]
  calc
    16 * (K : ℝ) ^ 2 * ((A : ℝ) / (N : ℝ) ^ d) / H =
        (16 * (K : ℝ) ^ 2 * A / (N : ℝ) ^ d) * (1 / H) := by ring
    _ ≤ (16 * (K : ℝ) ^ 2 * A / (N : ℝ) ^ d) * (L / N) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by rw [pow_succ]; ring

private theorem leading_inverse_succ (d : ℕ) (hd : 0 < d) (n : ℕ)
    (δ : ℝ) (hδ : 0 < δ) (hbudget : 1 ≤ (n : ℝ) * δ)
    (ih : ∀ N : ℕ, 0 < N → ∀ p : Polynomial ℝ, p.natDegree ≤ d →
      δ ^ 2 / 4 ≤ ‖mean N (polynomialPhase p)‖ →
      ∃ q : ℕ, 0 < q ∧ q ≤ leadingInverseBudget d (4 * n ^ 2) ∧ ∃ m : ℤ,
        |(q : ℝ) * p.coeff d - m| ≤ (leadingInverseBudget d (4 * n ^ 2) : ℝ) / (N : ℝ) ^ d)
    (N : ℕ) (hN : 0 < N) (p : Polynomial ℝ) (hp : p.natDegree ≤ d + 1)
    (hlarge : δ ≤ ‖mean N (polynomialPhase p)‖) :
    ∃ q : ℕ, 0 < q ∧ q ≤ leadingInverseBudget (d + 1) n ∧ ∃ m : ℤ,
      |(q : ℝ) * p.coeff (d + 1) - m| ≤
        (leadingInverseBudget (d + 1) n : ℝ) / (N : ℝ) ^ (d + 1) := by
  let A := leadingInverseBudget d (4 * n ^ 2)
  let M := 16 * n ^ 2
  let K := 4 * A * n ^ 2
  have hA := leadingInverseBudget_pos d (4 * n ^ 2)
  have hn : 0 < n := by
    by_contra! hn
    rw [Nat.eq_zero_of_le_zero hn, Nat.cast_zero, zero_mul] at hbudget
    exact (not_le_of_gt zero_lt_one) hbudget
  have hMnat : 0 < M := by dsimp [M]; positivity
  have hKnat : 0 < K := by dsimp [K]; positivity
  have hM₀ : 0 < (M : ℝ) := Nat.cast_pos.mpr hMnat
  have hK₀ : 0 < (K : ℝ) := Nat.cast_pos.mpr hKnat
  have hsq : 1 ≤ ((n : ℝ) * δ) ^ 2 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hbudget 2
  have hMδ : 16 ≤ (M : ℝ) * δ ^ 2 := by
    dsimp [M]
    push_cast
    nlinarith only [hsq]
  have hKδ : 4 * (A : ℝ) ≤ (K : ℝ) * δ ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hsq (show 0 ≤ 4 * (A : ℝ) by positivity)
    dsimp [K]
    push_cast
    nlinarith only [h]
  let T := M * (32 * K ^ 2 + 1) + 16 * K * A + 2 * M + 1
  let Q := 2 * K * A * (d + 1)
  let C := 32 * K ^ 2 * A * M
  let B := Q + C + T ^ (d + 1) + 1
  have hB : 0 < B := by dsimp [B]; omega
  have hBudget : leadingInverseBudget (d + 1) n = B := by
    cases d with
    | zero => omega
    | succ d => rfl
  have hQB : Q ≤ B := by dsimp [B]; omega
  have hCB : C ≤ B := by dsimp [B]; omega
  have hTB : T ^ (d + 1) ≤ B := by dsimp [B]; omega
  rw [hBudget]
  have hN₀ : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  by_cases hNT : N < T
  · refine ⟨1, by omega, hB, ⌊p.coeff (d + 1)⌋, ?_⟩
    simp only [Nat.cast_one, one_mul]
    calc
      |p.coeff (d + 1) - (⌊p.coeff (d + 1)⌋ : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
        linarith [Int.lt_floor_add_one (p.coeff (d + 1))]
      _ ≤ (B : ℝ) / (N : ℝ) ^ (d + 1) := by
        apply (le_div_iff₀ (pow_pos hN₀ _)).mpr
        simp only [one_mul]
        exact_mod_cast (Nat.pow_le_pow_left hNT.le (d + 1)).trans hTB
  · have hTN : T ≤ N := Nat.le_of_not_gt hNT
    let H := N / M
    have hHsize : 32 * K ^ 2 ≤ H := by
      apply (Nat.le_div_iff_mul_le hMnat).mpr
      have he : M * (32 * K ^ 2 + 1) = 32 * K ^ 2 * M + M := by ring
      dsimp [T] at hTN
      rw [he] at hTN
      omega
    have hH : 0 < H := lt_of_lt_of_le (by positivity) hHsize
    have h16 : 16 * K * A ≤ N := by dsimp [T] at hTN; omega
    have hHM : (H : ℝ) * M ≤ N := by
      exact_mod_cast (Nat.div_mul_le_self N M)
    have hboundary : 4 * (H : ℝ) / N ≤ δ ^ 2 / 2 := by
      calc
        4 * (H : ℝ) / N ≤ 4 / (M : ℝ) := by
          apply (div_le_div_iff₀ hN₀ hM₀).mpr
          nlinarith only [hHM]
        _ ≤ δ ^ 2 / 2 := by
          apply (div_le_iff₀ hM₀).mpr
          nlinarith only [hMδ]
    have hdensity : (1 : ℝ) / K ≤ δ ^ 2 / (4 * A) := by
      apply (div_le_div_iff₀ hK₀ (by positivity : 0 < 4 * (A : ℝ))).mpr
      nlinarith only [hKδ]
    have heps : (A : ℝ) / (N : ℝ) ^ d ≤ 1 / (16 * K) := by
      have hpow : (N : ℝ) ≤ (N : ℝ) ^ d :=
        le_self_pow₀ (by exact_mod_cast hN) (Nat.ne_of_gt hd)
      have h16' : 16 * (K : ℝ) * A ≤ N := by exact_mod_cast h16
      apply (div_le_div_iff₀ (pow_pos hN₀ _) (by positivity : 0 < 16 * (K : ℝ))).mpr
      nlinarith only [hpow, h16']
    have hHL : (N : ℝ) ≤ (H : ℝ) * (2 * M : ℕ) := by
      have hrem := Nat.mod_lt N hMnat
      have he := Nat.div_add_mod N M
      have hmH : M ≤ H * M := by nlinarith only [Nat.mul_le_mul_right M hH]
      have hh : N ≤ H * (2 * M) := by dsimp [H] at hmH ⊢; nlinarith only [he, hrem, hmH]
      exact_mod_cast hh
    obtain ⟨q, hq, hqQ, m, hm⟩ := leading_inverse_step_at_length d δ hδ A K (2 * M)
      N H hA hKnat hN hH hboundary hdensity hHsize heps hHL
      (ih N hN) p hp hlarge
    refine ⟨q, hq, hqQ.trans hQB, m, hm.trans ?_⟩
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hCB' : (C : ℝ) ≤ B := by exact_mod_cast hCB
    simp only [C, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hCB' ⊢
    nlinarith only [hCB']

theorem leading_inverse (d : ℕ) (hd : 0 < d) (B : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hB : 1 ≤ (B : ℝ) * δ)
    (N : ℕ) (hN : 0 < N) (p : Polynomial ℝ) (hp : p.natDegree ≤ d)
    (hlarge : δ ≤ ‖mean N (polynomialPhase p)‖) :
    ∃ q : ℕ, 0 < q ∧ q ≤ leadingInverseBudget d B ∧ ∃ m : ℤ,
      |(q : ℝ) * p.coeff d - m| ≤ (leadingInverseBudget d B : ℝ) / (N : ℝ) ^ d := by
  induction d generalizing B δ N p with
  | zero => omega
  | succ d ih =>
    by_cases he : d = 0
    · subst d
      exact leading_inverse_one B δ hδ hB N hN p hp hlarge
    · have hd' := Nat.pos_of_ne_zero he
      apply leading_inverse_succ d hd' B δ hδ hB _ N hN p hp hlarge
      intro M hM Q hQ hlargeQ
      have hsq : 1 ≤ ((B : ℝ) * δ) ^ 2 := by
        simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hB 2
      exact ih hd' (4 * B ^ 2) (δ ^ 2 / 4) (by positivity)
        (by push_cast; nlinarith only [hsq]) M hM Q hQ hlargeQ

end
end WeylInverse

open scoped BigOperators Polynomial

/-- The scalar inverse required by the dilation argument, for an arbitrary
translated interval. The explicit Weyl budget depends only on degree and
the reciprocal lower bound for the correlation. -/
theorem monomialPhaseInverse_Ico (k start len n : ℕ) {ρ L c : ℝ}
    (hk : 0 < k) (hlen : 0 < len) (hρ : 0 < ρ) (hn : 16 ≤ (n : ℝ) * ρ)
    (hL : 0 < L) (hcL : L ≤ c * (len : ℝ)) :
    let D := WeylInverse.leadingInverseBudget k n
    MonomialPhaseInverse (Finset.Ico start (start + len)) k D ρ ((D : ℝ) * c ^ k) L := by
  dsimp only
  intro θ b hphase
  let p : ℝ[X] := Polynomial.monomial k θ + Polynomial.C b
  let P : ℝ[X] := Polynomial.taylor (start : ℝ) p
  have hp : p.natDegree ≤ k := (Polynomial.natDegree_add_le _ _).trans
    (max_le (Polynomial.natDegree_monomial_le _) ((Polynomial.natDegree_C _).le.trans (Nat.zero_le _)))
  have hP : P.natDegree ≤ k := by simpa [P] using hp
  have hcoeff : P.coeff k = θ := by
    rw [WeylAverages.taylor_coeff_top p _ hp _]
    simp [p, Polynomial.coeff_C, hk.ne']
  have hab : Finset.Ico start (start + len) =
      (Finset.range len).image (fun x : ℕ => start + x) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hx
      exact ⟨x - start, by omega, by omega⟩
    · rintro ⟨n, hn, rfl⟩
      omega
  have hinj : Function.Injective (fun x : ℕ => start + x) := fun _ _ he =>
    Nat.add_left_cancel he
  have hcorr : ρ / 16 ≤ ‖WeylAverages.mean len (WeylAverages.polynomialPhase P)‖ := by
    rw [hab, Finset.expect_image hinj.injOn] at hphase
    simpa [WeylAverages.mean, WeylAverages.polynomialPhase, P, p, Polynomial.taylor_eval,
      Nat.cast_add, add_comm (start : ℝ)] using hphase
  obtain ⟨q, hq, hqD, a, ha⟩ := WeylInverse.leading_inverse k hk n (ρ / 16)
    (by positivity) (by linarith only [hn]) len hlen P hP hcorr
  refine ⟨q, hq, hqD, a, ?_⟩
  rw [hcoeff] at ha
  have hlenR : (0 : ℝ) < len := Nat.cast_pos.mpr hlen
  have hratio : L / (len : ℝ) ≤ c := (div_le_iff₀ hlenR).mpr hcL
  calc
    _ ≤ (WeylInverse.leadingInverseBudget k n : ℝ) / (len : ℝ) ^ k := ha
    _ = (WeylInverse.leadingInverseBudget k n : ℝ) * (L / (len : ℝ)) ^ k / L ^ k := by
      rw [div_pow]
      field_simp
    _ ≤ _ := by gcongr

end PrimeUniformity
