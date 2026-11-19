module

public import PrimeUniformity.Gowers
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators ComplexConjugate

/-- The vertex selected by a Boolean tuple of directions. -/
def cubeVertex {A : Type*} [AddCommMonoid A] {d : ℕ}
    (x : A) (h : Fin d → A) (v : Fin d → Bool) : A :=
  x + ∑ i, if v i then h i else 0

/-- The alternating conjugated product on the vertices of a cube. -/
def cubeProduct {A : Type*} [Add A] : (d : ℕ) → (A → ℂ) → A → (Fin d → A) → ℂ
  | 0, f, x, _ => f x
  | d + 1, f, x, h =>
    cubeProduct d f x (fun i => h i.succ) *
      conj (cubeProduct d f (x + h 0) (fun i => h i.succ))

private theorem cubeVertex_cons_false {A : Type*} [AddCommMonoid A] {d : ℕ}
    (x : A) (h : Fin (d + 1) → A) (v : Fin d → Bool) :
    cubeVertex x h (Fin.cons false v) = cubeVertex x (fun i => h i.succ) v := by
  simp [cubeVertex, Fin.sum_univ_succ]

private theorem cubeVertex_cons_true {A : Type*} [AddCommMonoid A] {d : ℕ}
    (x : A) (h : Fin (d + 1) → A) (v : Fin d → Bool) :
    cubeVertex x h (Fin.cons true v) = cubeVertex (x + h 0) (fun i => h i.succ) v := by
  simp [cubeVertex, Fin.sum_univ_succ, add_assoc]

/-- For real weights the alternating conjugations leave the ordinary
product of the vertex weights. -/
theorem cubeProduct_ofReal_eq_prod {A : Type*} [AddCommMonoid A] (d : ℕ)
    (f : A → ℝ) (x : A) (h : Fin d → A) :
    cubeProduct d (fun z => (f z : ℂ)) x h =
      ((∏ v : Fin d → Bool, f (cubeVertex x h v)) : ℝ) := by
  induction d generalizing x with
  | zero => simp [cubeProduct, cubeVertex]
  | succ d ih =>
    have he : (∏ v : Fin d.succ → Bool, f (cubeVertex x h v)) =
        (∏ v : Fin d → Bool, f (cubeVertex x (fun i => h i.succ) v)) *
        (∏ v : Fin d → Bool, f (cubeVertex (x + h 0) (fun i => h i.succ) v)) := by
      let e := Fin.consEquiv (fun _ : Fin d.succ => Bool)
      rw [← Equiv.prod_comp e (fun v => f (cubeVertex x h v))]
      rw [Fintype.prod_prod_type]
      change (∏ b : Bool, ∏ v : Fin d → Bool, f (cubeVertex x h (Fin.cons b v))) = _
      rw [Fintype.prod_bool]
      simp only [cubeVertex_cons_false, cubeVertex_cons_true]
      exact mul_comm _ _
    rw [cubeProduct, ih, ih, Complex.conj_ofReal, ← Complex.ofReal_mul, he]

/-- A cube product depends only on the values at its vertices. -/
theorem cubeProduct_congr {A B : Type*} [AddCommMonoid A] [AddCommMonoid B] (d : ℕ)
    (f : A → ℂ) (g : B → ℂ) (x : A) (y : B) (h : Fin d → A) (k : Fin d → B)
    (hv : ∀ v, f (cubeVertex x h v) = g (cubeVertex y k v)) :
    cubeProduct d f x h = cubeProduct d g y k := by
  induction d generalizing x y with
  | zero =>
    simpa [cubeProduct, cubeVertex] using hv (fun i => i.elim0)
  | succ d ih =>
    rw [cubeProduct, cubeProduct]
    congr 1
    · exact ih x y _ _ fun v => by
        simpa only [cubeVertex_cons_false] using hv (Fin.cons false v)
    · apply congrArg conj
      exact ih (x + h 0) (y + k 0) _ _ fun v => by
        simpa only [cubeVertex_cons_true] using hv (Fin.cons true v)

/-- A vertex outside the support makes the entire cube product vanish. -/
theorem cubeProduct_eq_zero_of_vertex {A : Type*} [AddCommMonoid A] (d : ℕ)
    (f : A → ℂ) (x : A) (h : Fin d → A) (v : Fin d → Bool)
    (hv : f (cubeVertex x h v) = 0) : cubeProduct d f x h = 0 := by
  induction d generalizing x with
  | zero => simpa [cubeProduct, cubeVertex] using hv
  | succ d ih =>
    have he : Fin.cons (v 0) (fun i : Fin d => v i.succ) = v := by
      funext i
      exact Fin.cases (by simp) (fun j => by simp) i
    cases hz : v 0 with
    | false =>
      rw [← he, hz, cubeVertex_cons_false] at hv
      simp only [cubeProduct, ih x _ _ hv, zero_mul]
    | true =>
      rw [← he, hz, cubeVertex_cons_true] at hv
      simp only [cubeProduct, ih (x + h 0) _ _ hv, map_zero, mul_zero]

/-- Cube products preserve pointwise multiplication. -/
theorem cubeProduct_mul {A : Type*} [Add A] (d : ℕ)
    (f g : A → ℂ) (x : A) (h : Fin d → A) :
    cubeProduct d (fun z => f z * g z) x h = cubeProduct d f x h * cubeProduct d g x h := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih =>
    simp only [cubeProduct, ih, map_mul]
    ac_rfl

/-- Conjugation commutes with cube products. -/
theorem cubeProduct_conj {A : Type*} [Add A] (d : ℕ)
    (f : A → ℂ) (x : A) (h : Fin d → A) :
    cubeProduct d (fun z => conj (f z)) x h = conj (cubeProduct d f x h) := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih => simp only [cubeProduct, ih, map_mul]

/-- Translation of the weight is translation of the cube. -/
theorem cubeProduct_translate {A : Type*} [AddCommSemigroup A] (d : ℕ)
    (f : A → ℂ) (x a : A) (h : Fin d → A) :
    cubeProduct d (fun z => f (z + a)) x h = cubeProduct d f (x + a) h := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih => simp only [cubeProduct, ih, add_right_comm x]

private theorem cubeProduct_difference {A : Type*} [AddCommSemigroup A] (d : ℕ)
    (f : A → ℂ) (x a : A) (h : Fin d → A) :
    cubeProduct d (difference a f) x h = cubeProduct d.succ f x (Fin.cons a h) := by
  change cubeProduct d (fun z => f z * conj (f (z + a))) x h = _
  simp [cubeProduct, cubeProduct_mul, cubeProduct_conj, cubeProduct_translate]

/-- The recursive Gowers cube moment is the normalized sum of the real
parts of the alternating cube products. -/
theorem gowersCubeMoment_eq_sum {K : Type*} [AddCommMonoid K] [Fintype K] (d : ℕ) (f : K → ℂ) :
    gowersCubeMoment d f =
      (∑ x : K, ∑ h : Fin d → K, (cubeProduct d f x h).re) / (Fintype.card K : ℝ) ^ (d + 1) := by
  classical
  induction d generalizing f with
  | zero => simp [gowersCubeMoment, meanC, cubeProduct, Complex.re_sum]
  | succ d ih =>
    simp only [gowersCubeMoment, meanR, ih, cubeProduct_difference]
    simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    rw [mul_assoc, ← mul_inv, ← pow_succ]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Fintype.sum_prod_type' (fun a h => (cubeProduct d.succ f x (Fin.cons a h)).re)]
    exact (Equiv.sum_comp (Fin.consEquiv fun _ : Fin d.succ => K)
      (fun h => (cubeProduct d.succ f x h).re))

end PrimeUniformity
