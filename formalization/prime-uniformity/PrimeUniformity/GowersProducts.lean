module

public import PrimeUniformity.GowersSum
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators ComplexConjugate

private theorem meanC_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℂ) : meanC (fun a => f (e a)) = meanC f := by
  simp only [meanC, Fintype.card_congr e, Equiv.sum_comp e f]

private theorem meanR_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) : meanR (fun a => f (e a)) = meanR f := by
  simp only [meanR, Fintype.card_congr e, Equiv.sum_comp e f]

private theorem meanC_prod_mul {A B : Type*} [Fintype A] [Fintype B]
    (f : A → ℂ) (g : B → ℂ) :
    meanC (fun a : A × B => f a.1 * g a.2) = meanC f * meanC g := by
  rw [meanC, meanC, meanC, Fintype.sum_prod_type' (fun x y => f x * g y), Fintype.card_prod,
    Nat.cast_mul, div_mul_div_comm]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

private theorem meanR_prod_mul {A B : Type*} [Fintype A] [Fintype B]
    (f : A → ℝ) (g : B → ℝ) :
    meanR (fun a : A × B => f a.1 * g a.2) = meanR f * meanR g := by
  rw [meanR, meanR, meanR, Fintype.sum_prod_type' (fun x y => f x * g y), Fintype.card_prod,
    Nat.cast_mul, div_mul_div_comm]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

private theorem cubeProduct_prod {A B : Type*} [Add A] [Add B] (d : ℕ)
    (f : A → ℂ) (g : B → ℂ) (x : A × B) (h : Fin d → A × B) :
    cubeProduct d (fun a : A × B => f a.1 * g a.2) x h =
      cubeProduct d f x.1 (fun i => (h i).1) * cubeProduct d g x.2 (fun i => (h i).2) := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih =>
    simp only [cubeProduct, ih, Prod.fst_add, Prod.snd_add, map_mul]
    ac_rfl

/-- The moment is invariant under an additive change of finite ambient group. -/
theorem gowersCubeMoment_comp_addEquiv {A B : Type*} [Add A] [Add B] [Fintype A] [Fintype B]
    (d : ℕ) (e : A ≃+ B) (f : B → ℂ) :
    gowersCubeMoment d (fun a => f (e a)) = gowersCubeMoment d f := by
  induction d generalizing f with
  | zero =>
    exact congrArg Complex.re (meanC_equiv e.toEquiv f)
  | succ d ih =>
    have hdiff (h : A) : difference h (fun a => f (e a)) =
        fun a => difference (e h) f (e a) := by
      funext a
      simp only [difference, map_add]
    simp_rw [gowersCubeMoment, hdiff, ih]
    exact meanR_equiv e.toEquiv (fun h => gowersCubeMoment d (difference h f))

/-- Positive-order cube moments multiply under tensor products. -/
theorem gowersCubeMoment_prod {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Fintype A] [Fintype B] (d : ℕ) (f : A → ℂ) (g : B → ℂ) :
    gowersCubeMoment d.succ (fun a : A × B => f a.1 * g a.2) =
      gowersCubeMoment d.succ f * gowersCubeMoment d.succ g := by
  rw [gowersCubeMoment_succ_eq_mean_norm_sq, gowersCubeMoment_succ_eq_mean_norm_sq,
    gowersCubeMoment_succ_eq_mean_norm_sq]
  let F (h : Fin d → A) := ‖meanC (fun x => cubeProduct d f x h)‖ ^ 2
  let G (h : Fin d → B) := ‖meanC (fun x => cubeProduct d g x h)‖ ^ 2
  let e := Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => A) (fun _ => B)
  trans meanR (fun h => F (e h).1 * G (e h).2)
  · congr 1
    funext h
    change ‖meanC (fun x => cubeProduct d (fun a : A × B => f a.1 * g a.2) x h)‖ ^ 2 =
      F (e h).1 * G (e h).2
    simp only [cubeProduct_prod]
    rw [meanC_prod_mul (fun x => cubeProduct d f x (fun i => (h i).1))
      (fun y => cubeProduct d g y (fun i => (h i).2)), norm_mul, mul_pow]
    rfl
  · rw [meanR_equiv e (fun a => F a.1 * G a.2), meanR_prod_mul]

/-- Factoring the modulus by the Chinese remainder theorem factors the
moment of the product of weights from the two coprime moduli. -/
theorem gowersCubeMoment_chineseRemainder {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (d : ℕ) (f : ZMod m → ℂ) (g : ZMod n → ℂ) :
    gowersCubeMoment d.succ (fun a : ZMod (m * n) =>
      f ((ZMod.chineseRemainder h) a).1 * g ((ZMod.chineseRemainder h) a).2) =
        gowersCubeMoment d.succ f * gowersCubeMoment d.succ g := by
  exact (gowersCubeMoment_comp_addEquiv d.succ (ZMod.chineseRemainder h).toAddEquiv
    (fun a : ZMod m × ZMod n => f a.1 * g a.2)).trans (gowersCubeMoment_prod d f g)

end PrimeUniformity
