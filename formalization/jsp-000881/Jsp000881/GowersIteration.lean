module

public import Jsp000881.GowersStep
import all Jsp000881.GowersStep
public import PrimeUniformity.Gowers
public import Lean.Elab.Tactic.Omega

public section

namespace Jsp000881

export PrimeUniformity (gowersCubeMoment)

open scoped BigOperators ComplexConjugate

structure LinearDirection (K : Type*) [Field K] where
  a : K
  b : K
  nonzero : a ≠ 0 ∨ b ≠ 0

noncomputable def LinearDirection.kernel {K : Type*} [Field K] (d : LinearDirection K) (w : K) : K × K :=
  (rowCoordinates d.a d.b d.nonzero).symm (0, w)

structure BoundedAffineWeight (K : Type*) [Field K] where
  dir : LinearDirection K
  c : K
  weight : K → ℂ
  norm_le_one : ∀ x, ‖weight x‖ ≤ 1

def BoundedAffineWeight.eval {K : Type*} [Field K] (g : BoundedAffineWeight K) (x : K × K) : ℂ :=
  g.weight (linearRow g.dir.a g.dir.b x + g.c)

def BoundedAffineWeight.differentiate {K : Type*} [Field K] (g : BoundedAffineWeight K)
    (h : K × K) : BoundedAffineWeight K :=
  { dir := g.dir
    c := g.c
    weight := difference (linearRow g.dir.a g.dir.b h) g.weight
    norm_le_one := difference_norm_le_one _ _ g.norm_le_one }

theorem BoundedAffineWeight.differentiate_eval {K : Type*} [Field K] (g : BoundedAffineWeight K)
    (h x : K × K) : (g.differentiate h).eval x = difference h g.eval x :=
  (difference_linearRow g.dir.a g.dir.b g.c h x g.weight).symm

def affineWeightProduct {K : Type*} [Field K] (x : K × K) : List (BoundedAffineWeight K) → ℂ
  | [] => 1
  | g :: gs => g.eval x * affineWeightProduct x gs

private theorem difference_mul {A : Type*} [Add A] (h : A) (f g : A → ℂ) (x : A) :
    difference h (fun y => f y * g y) x = difference h f x * difference h g x := by
  simp only [difference, map_mul]
  ring

private theorem difference_affineWeightProduct {K : Type*} [Field K]
    (h x : K × K) (gs : List (BoundedAffineWeight K)) :
    difference h (fun y => affineWeightProduct y gs) x =
      affineWeightProduct x (gs.map fun g => g.differentiate h) := by
  induction gs with
  | nil => simp [difference, affineWeightProduct]
  | cons g gs ih =>
    simp only [affineWeightProduct, List.map_cons, difference_mul,
      BoundedAffineWeight.differentiate_eval, ih]

/-- Average of the successive additive differences of a test weight. -/
noncomputable def directionalMoment {K : Type*} [Field K] [Fintype K] :
    List (LinearDirection K) → (K × K → ℂ) → ℝ
  | [], f => (meanC f).re
  | d :: ds, f => meanR fun w => directionalMoment ds (difference (d.kernel w) f)

/-- Iterated directional Cauchy–Schwarz for any number of bounded affine
companions. Five companions give the power (2^5). -/
theorem iterated_directional_cauchy_schwarz {K : Type*} [Field K] [Fintype K] (n : ℕ) :
    ∀ (gs : List (BoundedAffineWeight K)), gs.length = n + 1 → ∀ (f : K × K → ℂ),
      ‖meanC (fun x => f x * affineWeightProduct x gs)‖ ^ (2 ^ (n + 1)) ≤
        directionalMoment (gs.map BoundedAffineWeight.dir) f := by
  induction n with
  | zero =>
    intro gs hgs f
    cases gs with
    | nil => simp at hgs
    | cons g gs =>
      have hg : gs = [] := List.length_eq_zero_iff.mp (Nat.succ.inj hgs)
      subst gs
      simp only [Nat.zero_add, pow_one, List.map_cons, List.map_nil, directionalMoment,
        affineWeightProduct, mul_one, BoundedAffineWeight.eval, LinearDirection.kernel, meanC_re_eq_meanR,
        difference]
      simpa only [mul_comm] using directional_cauchy_schwarz_mean
        g.dir.a g.dir.b g.c g.dir.nonzero g.weight f g.norm_le_one
  | succ n ih =>
    intro gs hgs f
    cases gs with
    | nil => simp at hgs
    | cons g tail =>
      have hlen : tail.length = n + 1 := by simpa [Nat.succ_eq_add_one] using Nat.succ.inj hgs
      have hpow : (0 : ℕ) < 2 ^ (n + 1) := by positivity
      let m := 2 ^ (n + 1) - 1
      have hm : m + 1 = 2 ^ (n + 1) := by dsimp [m]; omega
      let F := fun x => f x * affineWeightProduct x tail
      have he (x : K × K) : f x * affineWeightProduct x (g :: tail) = g.eval x * F x := by
        simp only [affineWeightProduct, F]
        ring
      simp_rw [he]
      have hcs := directional_cauchy_schwarz_power
        g.dir.a g.dir.b g.c g.dir.nonzero g.weight F g.norm_le_one m
      rw [hm, mul_comm 2, ← pow_succ] at hcs
      refine hcs.trans ?_
      change (meanR fun w => ‖meanC (difference (g.dir.kernel w) F)‖ ^ (2 ^ (n + 1))) ≤ _
      simp only [List.map_cons, directionalMoment]
      apply meanR_mono
      intro w
      let H := g.dir.kernel w
      have hderiv : difference H F = fun x =>
          difference H f x * affineWeightProduct x (tail.map fun t => t.differentiate H) := by
        funext x
        simp only [F, difference_mul, difference_affineWeightProduct]
      rw [hderiv]
      have h := ih (tail.map fun t => t.differentiate H) (by simpa using hlen) (difference H f)
      rw [List.map_map] at h
      have hdir : BoundedAffineWeight.dir ∘ (fun t : BoundedAffineWeight K => t.differentiate H) =
          BoundedAffineWeight.dir := rfl
      rw [hdir] at h
      exact h

private theorem meanC_comp_row {K : Type*} [Field K] [Fintype K]
    (d : LinearDirection K) (c : K) (f : K → ℂ) :
    meanC (fun x => f (linearRow d.a d.b x + c)) = meanC f := by
  classical
  let e := rowCoordinates d.a d.b d.nonzero
  have hsum : (∑ x, f (linearRow d.a d.b x + c)) = ∑ uv : K × K, f (uv.1 + c) := by
    apply Fintype.sum_equiv e
    intro x
    rw [show (e x).1 = linearRow d.a d.b x from rowCoordinates_fst _ _ _ _]
  unfold meanC
  rw [hsum, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
  rw [← Finset.mul_sum]
  have he : (∑ x, f (x + c)) = ∑ x, f x := Equiv.sum_comp (Equiv.addRight c) f
  rw [he]
  have hcard : (Fintype.card K : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos.ne' : Fintype.card K ≠ 0)
  field_simp [hcard] <;> ring

/-- The directional cube moment of a single affine target equals the
one-dimensional Gowers cube moment when each direction is independent of
the target row. -/
theorem directionalMoment_on_row {K : Type*} [Field K] [Fintype K]
    (dirs : List (LinearDirection K)) (d : LinearDirection K) (c : K)
    (h : ∀ v ∈ dirs, v.a * d.b - v.b * d.a ≠ 0) (f : K → ℂ) :
    directionalMoment dirs (fun x => f (linearRow d.a d.b x + c)) =
      gowersCubeMoment dirs.length f := by
  induction dirs generalizing f with
  | nil =>
    simp only [directionalMoment, List.length_nil, gowersCubeMoment, meanC_comp_row]
  | cons v vs ih =>
    have hhead := h v List.mem_cons_self
    have htail : ∀ z ∈ vs, z.a * d.b - z.b * d.a ≠ 0 :=
      fun z hz => h z (List.mem_cons_of_mem v hz)
    let F := fun w => linearRow d.a d.b (v.kernel w)
    have hF : Function.Bijective F :=
      independent_row_on_kernel_bijective v.a v.b d.a d.b v.nonzero hhead
    let e := Equiv.ofBijective F hF
    calc
      _ = meanR (fun w => directionalMoment vs (fun x =>
          difference (F w) f (linearRow d.a d.b x + c))) := by
        simp only [directionalMoment]
        apply congrArg meanR
        funext w
        apply congrArg (directionalMoment vs)
        funext x
        exact difference_linearRow d.a d.b c (v.kernel w) x f
      _ = meanR (fun w => gowersCubeMoment vs.length (difference (F w) f)) := by
        apply congrArg meanR
        funext w
        exact ih htail _
      _ = meanR (fun w => gowersCubeMoment vs.length (difference w f)) := by
        unfold meanR
        exact congrArg (fun x : ℝ => x / (Fintype.card K : ℝ))
          (Equiv.sum_comp e (fun w => gowersCubeMoment vs.length (difference w f)))
      _ = _ := by simp only [List.length_cons, gowersCubeMoment]

theorem affine_system_gowers_bound {K : Type*} [Field K] [Fintype K] (n : ℕ)
    (gs : List (BoundedAffineWeight K)) (hlen : gs.length = n + 1)
    (d : LinearDirection K) (c : K)
    (h : ∀ g ∈ gs, g.dir.a * d.b - g.dir.b * d.a ≠ 0) (f : K → ℂ) :
    ‖meanC (fun x => f (linearRow d.a d.b x + c) * affineWeightProduct x gs)‖ ^ (2 ^ (n + 1)) ≤
      gowersCubeMoment (n + 1) f := by
  have hh : ∀ v ∈ gs.map BoundedAffineWeight.dir, v.a * d.b - v.b * d.a ≠ 0 := by
    intro v hv
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hv
    exact h g hg
  have hb := iterated_directional_cauchy_schwarz n gs hlen (fun x => f (linearRow d.a d.b x + c))
  rw [directionalMoment_on_row _ d c hh f, List.length_map, hlen] at hb
  exact hb

end Jsp000881
