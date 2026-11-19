module

public import PrimeUniformity.CubeLift
public import PrimeUniformity.CubeProduct
public import PrimeUniformity.Estimate
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PrimeUniformity

open scoped BigOperators

/-- The zero extension of a real weight on the integer interval `[1, X]`. -/
noncomputable def intervalWeight (X : ℕ) (w : ℤ → ℝ) (n : ℤ) : ℂ :=
  if 1 ≤ n ∧ n ≤ (X : ℤ) then (w n : ℂ) else 0

/-- The one-based integer representative of an element of `Fin X`. -/
def intervalEndpoint {X : ℕ} (i : Fin X) : ℤ := (i.val : ℤ) + 1

theorem intervalEndpoint_mem {X : ℕ} (i : Fin X) :
    1 ≤ intervalEndpoint i ∧ intervalEndpoint i ≤ (X : ℤ) := by
  have hi := i.isLt
  unfold intervalEndpoint
  omega

private theorem cubeVertex_eq_filter_sum {A : Type*} [AddCommMonoid A] {d : ℕ}
    (b : A) (h : Fin d → A) (v : Fin d → Bool) :
    cubeVertex b h v = b + ∑ i ∈ Finset.univ.filter (fun i => v i = true), h i := by
  simp [cubeVertex, Finset.sum_filter]

private theorem cubeVertex_all_false {A : Type*} [AddCommMonoid A] {d : ℕ}
    (b : A) (h : Fin d → A) : cubeVertex b h (fun _ => false) = b := by
  simp [cubeVertex]

private theorem cubeVertex_singleton {A : Type*} [AddCommMonoid A] {d : ℕ}
    (b : A) (h : Fin d → A) (j : Fin d) :
    cubeVertex b h (fun i => decide (i = j)) = b + h j := by
  simp [cubeVertex, Finset.sum_ite_eq']

private theorem cast_endpoint_val {X p : ℕ} [NeZero p] (hXp : X < p) (i : Fin X) :
    (((intervalEndpoint i : ℤ) : ZMod p).val : ℤ) = intervalEndpoint i := by
  have hp : (X : ℤ) < (p : ℤ) := by exact_mod_cast hXp
  rw [ZMod.val_intCast,
    Int.emod_eq_of_lt (by have := (intervalEndpoint_mem i).1; omega) ((intervalEndpoint_mem i).2.trans_lt hp)]

private theorem cast_endpoint_injective {X p : ℕ} [NeZero p] (hXp : X < p) :
    Function.Injective (fun i : Fin X => (intervalEndpoint i : ZMod p)) := by
  intro i j hij
  have hv := congrArg (fun z : ZMod p => (z.val : ℤ)) hij
  rw [cast_endpoint_val hXp, cast_endpoint_val hXp] at hv
  apply Fin.ext
  unfold intervalEndpoint at hv
  omega

private theorem exists_cast_endpoint {X p : ℕ} [NeZero p] (z : ZMod p)
    (hz : 1 ≤ z.val ∧ z.val ≤ X) : ∃ i : Fin X, (intervalEndpoint i : ZMod p) = z := by
  let i : Fin X := ⟨z.val - 1, by omega⟩
  refine ⟨i, ?_⟩
  have hi : intervalEndpoint i = (z.val : ℤ) := by
    change ((z.val - 1 : ℕ) : ℤ) + 1 = (z.val : ℤ)
    omega
  rw [hi, Int.cast_natCast, ZMod.natCast_zmod_val]

private def cubeEmbedding {d X p : ℕ} [NeZero p] (hXp : X < p) :
    (Fin X × (Fin d → Fin X)) ↪ (ZMod p × (Fin d → ZMod p)) where
  toFun a := (intervalEndpoint a.1, fun i => (intervalEndpoint (a.2 i) : ZMod p) - intervalEndpoint a.1)
  inj' := by
    intro a b hab
    have hbase := congrArg Prod.fst hab
    change (intervalEndpoint a.1 : ZMod p) = (intervalEndpoint b.1 : ZMod p) at hbase
    have hsingle := congrArg Prod.snd hab
    refine Prod.ext (cast_endpoint_injective hXp hbase) ?_
    funext i
    apply cast_endpoint_injective (p := p) hXp
    have hi := congrFun hsingle i
    change (intervalEndpoint (a.2 i) : ZMod p) - intervalEndpoint a.1 =
      (intervalEndpoint (b.2 i) : ZMod p) - intervalEndpoint b.1 at hi
    rw [hbase] at hi
    exact sub_left_inj.mp hi

private theorem cubeEmbedding_mem {d X p : ℕ} [NeZero p] (hXp : X < p)
    (z : ZMod p × (Fin d → ZMod p))
    (hb : 1 ≤ z.1.val ∧ z.1.val ≤ X)
    (hs : ∀ i, 1 ≤ (z.1 + z.2 i).val ∧ (z.1 + z.2 i).val ≤ X) :
    z ∈ Finset.univ.map (cubeEmbedding hXp) := by
  obtain ⟨base, hbase⟩ := exists_cast_endpoint z.1 hb
  choose single hsingle using fun i => exists_cast_endpoint (z.1 + z.2 i) (hs i)
  apply Finset.mem_map.mpr
  refine ⟨(base, single), Finset.mem_univ _, Prod.ext hbase ?_⟩
  funext i
  change (intervalEndpoint (single i) : ZMod p) - intervalEndpoint base = z.2 i
  rw [hbase, hsingle, add_sub_cancel_left]

private theorem intervalWeight_eq_cyclic_at_vertex {d X p : ℕ} [NeZero p]
    (hXp : X < p) (hp : (2 * (d : ℤ) + 2) * X < (p : ℤ))
    (w : ℤ → ℝ) (a : Fin X × (Fin d → Fin X)) (v : Fin d → Bool) :
    intervalWeight X w (cubeVertex (intervalEndpoint a.1) (fun i => intervalEndpoint (a.2 i) - intervalEndpoint a.1) v) =
      cyclicWeight X p w (cubeVertex (cubeEmbedding hXp a).1 (cubeEmbedding hXp a).2 v) := by
  let b := intervalEndpoint a.1
  let s (i : Fin d) := intervalEndpoint (a.2 i)
  let I := Finset.univ.filter (fun i => v i = true)
  let u := b + ∑ i ∈ I, (s i - b)
  let z : ZMod p := b + ∑ i ∈ I, ((s i : ZMod p) - (b : ZMod p))
  simp only [cubeVertex_eq_filter_sum]
  change intervalWeight X w u = cyclicWeight X p w z
  by_cases hu : 1 ≤ u ∧ u ≤ (X : ℤ)
  · have huz : (u : ZMod p) = z := by simp only [u, z, Int.cast_add, Int.cast_sum, Int.cast_sub]
    rw [← huz, cyclicWeight_intCast hXp w hu.1 hu.2, intervalWeight, if_pos hu]
  · rw [intervalWeight, if_neg hu, cyclicWeight]
    split
    · rename_i hz
      have abs_le_of_mem : ∀ n : ℤ, 1 ≤ n → n ≤ (X : ℤ) → |n| ≤ (X : ℤ) := by
        intro n hn hX
        simpa only [abs_of_nonneg (show 0 ≤ n by omega)] using hX
      have hz₁ : 1 ≤ (z.val : ℤ) := by exact_mod_cast hz.1
      have hz₂ : (z.val : ℤ) ≤ (X : ℤ) := by exact_mod_cast hz.2
      have hb := intervalEndpoint_mem a.1
      have hcard : I.card ≤ d := by simpa using Finset.card_le_univ I
      have hcast : ((z.val : ℤ) : ZMod p) = z := by
        rw [Int.cast_natCast, ZMod.natCast_zmod_val]
      have heq : (z.val : ℤ) = u :=
        cube_vertex_eq_of_representatives I s (b : ZMod p)
          (fun i => (s i : ZMod p) - (b : ZMod p))
          (abs_le_of_mem b hb.1 hb.2) (abs_le_of_mem _ hz₁ hz₂)
          (fun i _ => abs_le_of_mem _ (intervalEndpoint_mem (a.2 i)).1 (intervalEndpoint_mem (a.2 i)).2)
          hcard hp rfl (fun i _ => by simp) hcast
      exact (hu ⟨heq ▸ hz₁, heq ▸ hz₂⟩).elim
    · rfl

/-- The unnormalized real cube sum on `[1, X]`. The parameters are the
base and singleton endpoints. All other vertices use the zero extension. -/
noncomputable def intervalCubeSum (d X : ℕ) (w : ℤ → ℝ) : ℝ :=
  ∑ a : Fin X × (Fin d → Fin X),
    (cubeProduct d (intervalWeight X w) (intervalEndpoint a.1)
      (fun i => intervalEndpoint (a.2 i) - intervalEndpoint a.1)).re

/-- For a sufficiently large prime modulus the only difference between the
integer cube sum and the cyclic cube moment is the cyclic normalization. -/
theorem gowersCubeMoment_cyclicWeight_eq_intervalCubeSum (d X p : ℕ) [Fact p.Prime]
    (hXp : X < p) (hp : (2 * (d : ℤ) + 2) * X < (p : ℤ)) (w : ℤ → ℝ) :
    gowersCubeMoment d (cyclicWeight X p w) = intervalCubeSum d X w / (p : ℝ) ^ (d + 1) := by
  classical
  rw [gowersCubeMoment_eq_sum, ZMod.card]
  congr 1
  let F (z : ZMod p × (Fin d → ZMod p)) := (cubeProduct d (cyclicWeight X p w) z.1 z.2).re
  rw [← Fintype.sum_prod_type' (fun x h => (cubeProduct d (cyclicWeight X p w) x h).re)]
  change ∑ z, F z = _
  trans ∑ z ∈ Finset.univ.map (cubeEmbedding hXp), F z
  · symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro z _ hz
    have vanish : ∀ v, ¬ (1 ≤ (cubeVertex z.1 z.2 v).val ∧
        (cubeVertex z.1 z.2 v).val ≤ X) → F z = 0 := by
      intro v hv
      unfold F
      rw [cubeProduct_eq_zero_of_vertex d _ z.1 z.2 v (by simp [cyclicWeight, hv]), Complex.zero_re]
    by_cases hb : 1 ≤ z.1.val ∧ z.1.val ≤ X
    · by_contra hn
      apply hz
      apply cubeEmbedding_mem hXp z hb
      intro i
      by_contra hi
      apply hn
      apply vanish (fun j => decide (j = i))
      rwa [cubeVertex_singleton]
    · apply vanish (fun _ => false)
      rwa [cubeVertex_all_false]
  · rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro a _
    apply congrArg Complex.re
    symm
    exact cubeProduct_congr d _ _ _ _ _ _ (intervalWeight_eq_cyclic_at_vertex hXp hp w a)

private theorem cubeProduct_eq_one_of_vertices {A : Type*} [AddCommMonoid A] (d : ℕ)
    (f : A → ℂ) (x : A) (h : Fin d → A)
    (hf : ∀ v, f (cubeVertex x h v) = 1) : cubeProduct d f x h = 1 := by
  have constant_one (n : ℕ) (a : A) (k : Fin n → A) :
      cubeProduct n (fun _ => 1) a k = 1 := by
    induction n generalizing a with
    | zero => rfl
    | succ n ih => simp only [cubeProduct, ih, map_one, mul_one]
  rw [cubeProduct_congr d f (fun _ => 1) x x h h hf, constant_one]

/-- The base and singleton endpoints of the cubes entirely in `[1, X]`. -/
noncomputable def intervalCubes (d X : ℕ) : Finset (Fin X × (Fin d → Fin X)) := by
  classical
  exact Finset.univ.filter (fun a => ∀ v : Fin d → Bool,
    let n := cubeVertex (intervalEndpoint a.1)
      (fun i => intervalEndpoint (a.2 i) - intervalEndpoint a.1) v
    1 ≤ n ∧ n ≤ (X : ℤ))

/-- The unit weight counts the integer cubes with all vertices in the interval. -/
theorem intervalCubeSum_one_eq_card (d X : ℕ) :
    intervalCubeSum d X (fun _ => 1) = (intervalCubes d X).card := by
  classical
  have hone : ((intervalCubes d X).card : ℝ) = ∑ _ ∈ intervalCubes d X, (1 : ℝ) := by simp
  rw [intervalCubeSum, hone, intervalCubes, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  split
  · rename_i h
    have hprod := cubeProduct_eq_one_of_vertices d (intervalWeight X (fun _ => 1))
      (intervalEndpoint a.1) (fun i => intervalEndpoint (a.2 i) - intervalEndpoint a.1)
      (fun v => by simp [intervalWeight, h v])
    simp [hprod]
  · rename_i h
    obtain ⟨v, hv⟩ := not_forall.mp h
    have hprod := cubeProduct_eq_zero_of_vertex d (intervalWeight X (fun _ => 1))
      (intervalEndpoint a.1) (fun i => intervalEndpoint (a.2 i) - intervalEndpoint a.1) v
      (by simp only [intervalWeight, if_neg hv])
    simp [hprod]

theorem intervalCubeSum_one_le (d X : ℕ) :
    intervalCubeSum d X (fun _ => 1) ≤ (X : ℝ) ^ (d + 1) := by
  rw [intervalCubeSum_one_eq_card]
  have h := Finset.card_le_univ (intervalCubes d X)
  have hcard : Fintype.card (Fin X × (Fin d → Fin X)) = X ^ (d + 1) := by
    simp [pow_succ, Nat.mul_comm]
  rw [hcard] at h
  exact_mod_cast h

/-- Integer cubes wholly contained in `[1, X]`, parameterized by their
increments and base point. -/
abbrev SupportedIntervalCube (d X : ℕ) :=
  {a : (Fin d → ℤ) × ℤ // ∀ v : Fin d → Bool,
    cubeVertex a.2 a.1 v ∈ Finset.Ico (1 : ℤ) (1 + (X : ℤ))}

/-- The zero-based index of an integer in the interval `[1, X]`. -/
def intervalIndex {X : ℕ} (n : ℤ) (hn : 1 ≤ n ∧ n ≤ (X : ℤ)) : Fin X :=
  ⟨(n - 1).toNat, by omega⟩

theorem intervalEndpoint_intervalIndex {X : ℕ} (n : ℤ) (hn : 1 ≤ n ∧ n ≤ (X : ℤ)) :
    intervalEndpoint (intervalIndex n hn) = n := by
  change (((n - 1).toNat : ℕ) : ℤ) + 1 = n
  omega

theorem intervalIndex_intervalEndpoint {X : ℕ} (i : Fin X) :
    intervalIndex (intervalEndpoint i) (intervalEndpoint_mem i) = i := by
  apply Fin.ext
  change (((i.val : ℤ) + 1) - 1).toNat = i.val
  omega

theorem supportedIntervalCube_mem {d X : ℕ} (a : SupportedIntervalCube d X)
    (v : Fin d → Bool) : 1 ≤ cubeVertex a.val.2 a.val.1 v ∧
      cubeVertex a.val.2 a.val.1 v ≤ (X : ℤ) := by
  have hv := Finset.mem_Ico.mp (a.property v)
  exact ⟨hv.1, by omega⟩

/-- Base and singleton endpoints encode exactly the supported integer cubes. -/
noncomputable def intervalCubesEquiv (d X : ℕ) :
    (intervalCubes d X : Type) ≃ SupportedIntervalCube d X := by
  classical
  let baseMem (a : SupportedIntervalCube d X) : 1 ≤ a.val.2 ∧ a.val.2 ≤ (X : ℤ) := by
    simpa only [cubeVertex_all_false] using supportedIntervalCube_mem a (fun _ => false)
  let singleMem (a : SupportedIntervalCube d X) (i : Fin d) :
      1 ≤ a.val.2 + a.val.1 i ∧ a.val.2 + a.val.1 i ≤ (X : ℤ) := by
    simpa only [cubeVertex_singleton] using supportedIntervalCube_mem a (fun j => decide (j = i))
  refine {
    toFun := fun a => ⟨(fun i => intervalEndpoint (a.val.2 i) - intervalEndpoint a.val.1,
      intervalEndpoint a.val.1), ?_⟩
    invFun := fun a => ⟨(intervalIndex a.val.2 (baseMem a),
      fun i => intervalIndex (a.val.2 + a.val.1 i) (singleMem a i)), ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro v
    have ha := (Finset.mem_filter.mp (show a.val ∈ intervalCubes d X from a.property)).2 v
    have hupper : cubeVertex (intervalEndpoint a.val.1)
        (fun i => intervalEndpoint (a.val.2 i) - intervalEndpoint a.val.1) v < 1 + (X : ℤ) := by omega
    exact Finset.mem_Ico.mpr ⟨ha.1, hupper⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro v
    simp only [intervalEndpoint_intervalIndex, add_sub_cancel_left]
    exact supportedIntervalCube_mem a v
  · intro a
    apply Subtype.ext
    apply Prod.ext
    · exact intervalIndex_intervalEndpoint a.val.1
    · funext i
      apply Fin.ext
      change (intervalEndpoint a.val.1 + (intervalEndpoint (a.val.2 i) -
        intervalEndpoint a.val.1) - 1).toNat = (a.val.2 i).val
      rw [show intervalEndpoint a.val.1 + (intervalEndpoint (a.val.2 i) -
        intervalEndpoint a.val.1) = intervalEndpoint (a.val.2 i) by omega]
      unfold intervalEndpoint
      omega
  · intro a
    apply Subtype.ext
    apply Prod.ext
    · funext i
      simp only [intervalEndpoint_intervalIndex, add_sub_cancel_left]
    · exact intervalEndpoint_intervalIndex a.val.2 (baseMem a)

noncomputable instance supportedIntervalCubeFintype (d X : ℕ) :
    Fintype (SupportedIntervalCube d X) :=
  Fintype.ofEquiv (intervalCubes d X : Type) (intervalCubesEquiv d X)

private theorem intervalCubeSum_eq_sum_intervalCubes (d X : ℕ) (w : ℤ → ℝ) :
    intervalCubeSum d X w = ∑ a ∈ intervalCubes d X,
      ∏ v : Fin d → Bool, w (cubeVertex (intervalEndpoint a.1)
        (fun i => intervalEndpoint (a.2 i) - intervalEndpoint a.1) v) := by
  classical
  let P (a : Fin X × (Fin d → Fin X)) := (cubeProduct d (intervalWeight X w)
    (intervalEndpoint a.1) (fun i => intervalEndpoint (a.2 i) - intervalEndpoint a.1)).re
  have hsum : (∑ a ∈ intervalCubes d X, P a) = ∑ a, P a := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ ha
    have hb : ¬ ∀ v : Fin d → Bool,
        let n := cubeVertex (intervalEndpoint a.1)
          (fun i => intervalEndpoint (a.2 i) - intervalEndpoint a.1) v
        1 ≤ n ∧ n ≤ (X : ℤ) := by
      intro hp
      exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hp⟩)
    obtain ⟨v, hv⟩ := not_forall.mp hb
    unfold P
    rw [cubeProduct_eq_zero_of_vertex d _ _ _ v (by simp only [intervalWeight, if_neg hv]), Complex.zero_re]
  rw [intervalCubeSum]
  change (∑ a, P a) = _
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro a ha
  let b := intervalEndpoint a.1
  let h (i : Fin d) := intervalEndpoint (a.2 i) - b
  have hb : ∀ v, 1 ≤ cubeVertex b h v ∧ cubeVertex b h v ≤ (X : ℤ) :=
    (Finset.mem_filter.mp (show a ∈ intervalCubes d X from ha)).2
  have he := cubeProduct_congr d (intervalWeight X w) (fun n => (w n : ℂ)) b b h h
    (fun v => by simp only [intervalWeight, if_pos (hb v)])
  change (cubeProduct d (intervalWeight X w) b h).re = _
  rw [he, cubeProduct_ofReal_eq_prod, Complex.ofReal_re]

/-- The normalized interval moment also equals the ordinary average over
supported cubes in increment coordinates. -/
theorem normalizedIntervalCubeSum_eq_supportedCubeAverage (d X : ℕ) (w : ℤ → ℝ) :
    intervalCubeSum d X w / intervalCubeSum d X (fun _ => 1) =
      (∑ a : SupportedIntervalCube d X, ∏ v : Fin d → Bool,
        w (cubeVertex a.val.2 a.val.1 v)) / (Nat.card (SupportedIntervalCube d X) : ℝ) := by
  rw [intervalCubeSum_eq_sum_intervalCubes, intervalCubeSum_one_eq_card]
  have hcard := Nat.card_congr (intervalCubesEquiv d X)
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hcard
  rw [hcard]
  congr 1
  rw [← Finset.sum_coe_sort]
  exact Equiv.sum_comp (intervalCubesEquiv d X)
    (fun a => ∏ v : Fin d → Bool, w (cubeVertex a.val.2 a.val.1 v))

/-- Multiplying the weight by a real constant multiplies the interval
cube sum by one copy of the constant per vertex. -/
theorem intervalCubeSum_mul_const (d X : ℕ) (a : ℝ) (w : ℤ → ℝ) :
    intervalCubeSum d X (fun n => a * w n) = a ^ (2 ^ d : ℕ) * intervalCubeSum d X w := by
  rw [intervalCubeSum_eq_sum_intervalCubes, intervalCubeSum_eq_sum_intervalCubes, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  simp

/-- The interval cube moment estimate for the prime-minus-Cramér weight.
The unit-weight cube sum is the normalization of the interval moment. -/
def IntervalGowersUniformityEstimate (order exponent : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in Filter.atTop,
    intervalCubeSum order X (fun n => primeWeight n - cramerWeight (primeUniformityCutoff X) n) ≤
      (C / (Real.log (X : ℝ)) ^ exponent) * intervalCubeSum order X (fun _ => 1)

/-- The interval estimate suffices for the cyclic estimate used by the
arithmetic application, with the same logarithmic exponent and constant. -/
theorem gowersUniformityEstimate_of_interval (d A : ℕ)
    (h : IntervalGowersUniformityEstimate d A) : GowersUniformityEstimate d A := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [h, Filter.eventually_ge_atTop (2 : ℕ)] with X hX hX₂
  intro p hp hlo _
  let : Fact p.Prime := ⟨hp⟩
  have hXp : X < p :=
    lt_of_le_of_lt (by simpa using Nat.mul_le_mul_right X (show 1 ≤ 4 * (d + 3) by omega)) hlo
  have hstrong : (2 * (d : ℤ) + 2) * X < (p : ℤ) := by
    have hnat : (2 * d + 2) * X < p :=
      lt_of_le_of_lt (Nat.mul_le_mul_right X (by omega)) hlo
    exact_mod_cast hnat
  have hppos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hnormal : intervalCubeSum d X (fun _ => 1) ≤ (p : ℝ) ^ (d + 1) :=
    (intervalCubeSum_one_le d X).trans (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hXp.le) _)
  rw [primeCramerDifference, gowersCubeMoment_cyclicWeight_eq_intervalCubeSum d X p hXp hstrong,
    div_le_iff₀ (pow_pos hppos _)]
  exact hX.trans (mul_le_mul_of_nonneg_left hnormal (div_nonneg hC.le (pow_nonneg hlog _)))

end PrimeUniformity
