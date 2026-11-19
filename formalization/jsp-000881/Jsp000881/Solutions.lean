module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

public section

namespace Jsp000881

open scoped ArithmeticFunction.sigma

structure PrimeTuple where
  p1 : ℕ
  p2 : ℕ
  p3 : ℕ
  p4 : ℕ
  p5 : ℕ
  p6 : ℕ
  deriving DecidableEq

def PrimeTuple.solution (s : PrimeTuple) : ℕ × ℕ :=
  (54000 * s.p1 * s.p2, 111600 * s.p3 * s.p4)

def PrimeTuple.LiEquations (s : PrimeTuple) : Prop :=
  (15 * s.p1 * s.p2 + 31 * s.p3 * s.p4 = 508 * s.p5 * s.p6) ∧
  (15 * (s.p1 + s.p2) + 31 * (s.p3 + s.p4) = 508 * (s.p5 + s.p6) + 462)

def PrimeTuple.IsOrderedFresh (s : PrimeTuple) : Prop :=
  s.p1.Prime ∧ s.p2.Prime ∧ s.p3.Prime ∧ s.p4.Prime ∧ s.p5.Prime ∧ s.p6.Prime ∧
  127 < s.p1 ∧ 127 < s.p3 ∧ 127 < s.p5 ∧
  s.p1 < s.p2 ∧ s.p3 < s.p4 ∧ s.p5 < s.p6

private theorem sigma_mul {a b : ℕ} (h : a.Coprime b) : σ 1 (a * b) = σ 1 a * σ 1 b :=
  ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

private theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  simpa [Finset.sum_range_succ, add_comm] using
    (ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp)

private theorem sigma_left : σ 1 54000 = 193440 := by
  have h2 : σ 1 16 = 31 := by
    rw [show 16 = 2 ^ 4 by decide, ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 2)] <;> decide
  have h3 : σ 1 27 = 40 := by
    rw [show 27 = 3 ^ 3 by decide, ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 3)] <;> decide
  have h5 : σ 1 125 = 156 := by
    rw [show 125 = 5 ^ 3 by decide, ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 5)] <;> decide
  rw [show 54000 = (16 * 27) * 125 by decide,
    sigma_mul (by decide : Nat.Coprime (16 * 27) 125),
    sigma_mul (by decide : Nat.Coprime 16 27), h2, h3, h5]

private theorem sigma_right : σ 1 111600 = 399776 := by
  have h2 : σ 1 16 = 31 := by
    rw [show 16 = 2 ^ 4 by decide, ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 2)] <;> decide
  have h3 : σ 1 9 = 13 := by
    rw [show 9 = 3 ^ 2 by decide, ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 3)] <;> decide
  have h5 : σ 1 25 = 31 := by
    rw [show 25 = 5 ^ 2 by decide, ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 5)] <;> decide
  rw [show 111600 = ((16 * 9) * 25) * 31 by decide,
    sigma_mul (by decide : Nat.Coprime ((16 * 9) * 25) 31),
    sigma_mul (by decide : Nat.Coprime (16 * 9) 25),
    sigma_mul (by decide : Nat.Coprime 16 9), h2, h3, h5, sigma_prime (by decide : Nat.Prime 31)]

private theorem sigma_perimeter : σ 1 1828800 = 6551168 := by
  have h2 : σ 1 64 = 127 := by
    rw [show 64 = 2 ^ 6 by decide, ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 2)] <;> decide
  have h3 : σ 1 9 = 13 := by
    rw [show 9 = 3 ^ 2 by decide, ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 3)] <;> decide
  have h5 : σ 1 25 = 31 := by
    rw [show 25 = 5 ^ 2 by decide, ArithmeticFunction.sigma_one_apply_prime_pow (by decide : Nat.Prime 5)] <;> decide
  rw [show 1828800 = ((64 * 9) * 25) * 127 by decide,
    sigma_mul (by decide : Nat.Coprime ((64 * 9) * 25) 127),
    sigma_mul (by decide : Nat.Coprime (64 * 9) 25),
    sigma_mul (by decide : Nat.Coprime 64 9), h2, h3, h5, sigma_prime (by decide : Nat.Prime 127)]

private theorem prime_not_dvd_small {p m : ℕ} (hm : 0 < m) (h : m < p) : ¬ p ∣ m :=
  fun hd => (not_le_of_gt h) (Nat.le_of_dvd hm hd)

private theorem coprime_left {p : ℕ} (hp : p.Prime) (h : 127 < p) : Nat.Coprime 54000 p := by
  rw [show 54000 = (16 * 27) * 125 by decide]
  apply (hp.coprime_iff_not_dvd.mpr ?_).symm
  exact hp.not_dvd_mul (hp.not_dvd_mul
    (prime_not_dvd_small (by decide) (by omega)) (prime_not_dvd_small (by decide) (by omega)))
    (prime_not_dvd_small (by decide) (by omega))

private theorem coprime_right {p : ℕ} (hp : p.Prime) (h : 127 < p) : Nat.Coprime 111600 p := by
  rw [show 111600 = ((16 * 9) * 25) * 31 by decide]
  apply (hp.coprime_iff_not_dvd.mpr ?_).symm
  exact hp.not_dvd_mul (hp.not_dvd_mul (hp.not_dvd_mul
    (prime_not_dvd_small (by decide) (by omega)) (prime_not_dvd_small (by decide) (by omega)))
    (prime_not_dvd_small (by decide) (by omega))) (prime_not_dvd_small (by decide) (by omega))

private theorem coprime_perimeter {p : ℕ} (hp : p.Prime) (h : 127 < p) : Nat.Coprime 1828800 p := by
  rw [show 1828800 = ((64 * 9) * 25) * 127 by decide]
  apply (hp.coprime_iff_not_dvd.mpr ?_).symm
  exact hp.not_dvd_mul (hp.not_dvd_mul (hp.not_dvd_mul
    (prime_not_dvd_small (by decide) (by omega)) (prime_not_dvd_small (by decide) (by omega)))
    (prime_not_dvd_small (by decide) (by omega))) (prime_not_dvd_small (by decide) h)

private theorem sigma_times_primes {a p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hap : a.Coprime p) (haq : a.Coprime q) :
    σ 1 (a * p * q) = σ 1 a * (p + 1) * (q + 1) := by
  have hqp : ¬ q ∣ p := prime_not_dvd_small hp.pos hpq
  have hqa : ¬ q ∣ a := hq.coprime_iff_not_dvd.mp haq.symm
  have h : (a * p).Coprime q := (hq.coprime_iff_not_dvd.mpr (hq.not_dvd_mul hqa hqp)).symm
  rw [sigma_mul h, sigma_mul hap, sigma_prime hp, sigma_prime hq]

theorem PrimeTuple.solution_perimeter {s : PrimeTuple} (h : s.LiEquations) :
    s.solution.1 + s.solution.2 = 1828800 * s.p5 * s.p6 := by
  obtain ⟨hp, _⟩ := h
  dsimp [solution]
  nlinarith only [hp]

theorem PrimeTuple.solution_positive {s : PrimeTuple} (hs : s.IsOrderedFresh) :
    0 < s.solution.1 ∧ 0 < s.solution.2 := by
  rcases hs with ⟨hp1, hp2, hp3, hp4, _, _, _, _, _, _, _, _⟩
  exact ⟨Nat.mul_pos (Nat.mul_pos (by decide) hp1.pos) hp2.pos,
    Nat.mul_pos (Nat.mul_pos (by decide) hp3.pos) hp4.pos⟩

theorem PrimeTuple.solution_sigma {s : PrimeTuple} (hs : s.IsOrderedFresh) (he : s.LiEquations) :
    σ 1 s.solution.1 + σ 1 s.solution.2 = σ 1 (s.solution.1 + s.solution.2) := by
  rcases hs with ⟨hp1, hp2, hp3, hp4, hp5, hp6, h1, h3, h5, h12, h34, h56⟩
  have hper := solution_perimeter he
  obtain ⟨hprod, hlin⟩ := he
  have hsft : 15 * (s.p1 + 1) * (s.p2 + 1) + 31 * (s.p3 + 1) * (s.p4 + 1) =
      508 * (s.p5 + 1) * (s.p6 + 1) := by
    nlinarith only [hprod, hlin]
  rw [hper]
  dsimp [solution]
  rw [sigma_times_primes hp1 hp2 h12 (coprime_left hp1 h1) (coprime_left hp2 (h1.trans h12)),
    sigma_times_primes hp3 hp4 h34 (coprime_right hp3 h3) (coprime_right hp4 (h3.trans h34)),
    sigma_times_primes hp5 hp6 h56 (coprime_perimeter hp5 h5) (coprime_perimeter hp6 (h5.trans h56)),
    sigma_left, sigma_right, sigma_perimeter]
  nlinarith only [hsft]

private theorem ordered_prime_factors_unique {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hs : s.Prime) (hpq : p < q) (hrs : r < s) (he : p * q = r * s) :
    p = r ∧ q = s := by
  have hpr : p ∣ r * s := he ▸ (dvd_mul_right p q)
  have hrp : r ∣ p * q := he.symm ▸ (dvd_mul_right r s)
  have hcases := (hp.dvd_mul.mp hpr).imp (Nat.prime_dvd_prime_iff_eq hp hr).mp
    (Nat.prime_dvd_prime_iff_eq hp hs).mp
  have hcases' := (hr.dvd_mul.mp hrp).imp (Nat.prime_dvd_prime_iff_eq hr hp).mp
    (Nat.prime_dvd_prime_iff_eq hr hq).mp
  have hfirst : p = r := by omega
  subst r
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hp.pos he⟩

theorem PrimeTuple.solution_injOn :
    Set.InjOn PrimeTuple.solution {s | s.IsOrderedFresh ∧ s.LiEquations} := by
  intro u hu v hv h
  have he1 : u.p1 * u.p2 = v.p1 * v.p2 := by
    have h1 := congrArg Prod.fst h
    simp only [solution] at h1
    nlinarith only [h1]
  have he2 : u.p3 * u.p4 = v.p3 * v.p4 := by
    have h2 := congrArg Prod.snd h
    simp only [solution] at h2
    nlinarith only [h2]
  have he3 : u.p5 * u.p6 = v.p5 * v.p6 := by
    have h3 := congrArg (fun p : ℕ × ℕ => p.1 + p.2) h
    change u.solution.1 + u.solution.2 = v.solution.1 + v.solution.2 at h3
    rw [solution_perimeter hu.2, solution_perimeter hv.2] at h3
    nlinarith only [h3]
  rcases hu.1 with ⟨hu1, hu2, hu3, hu4, hu5, hu6, _, _, _, hu12, hu34, hu56⟩
  rcases hv.1 with ⟨hv1, hv2, hv3, hv4, hv5, hv6, _, _, _, hv12, hv34, hv56⟩
  obtain ⟨h1, h2⟩ := ordered_prime_factors_unique hu1 hu2 hv1 hv2 hu12 hv12 he1
  obtain ⟨h3, h4⟩ := ordered_prime_factors_unique hu3 hu4 hv3 hv4 hu34 hv34 he2
  obtain ⟨h5, h6⟩ := ordered_prime_factors_unique hu5 hu6 hv5 hv6 hu56 hv56 he3
  cases u
  cases v
  congr <;> assumption

end Jsp000881
