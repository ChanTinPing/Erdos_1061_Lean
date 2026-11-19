module

public import Jsp000881.ModularDirections
import all Jsp000881.ModularDirections
public import Jsp000881.PrimeTriangle
import all Jsp000881.PrimeTriangle

public section

namespace Jsp000881

/-- Six actual affine rows, two translated interval cutoffs and one Gowers
input. The five companion weights contribute the fifth power of their bound. -/
theorem integralRows_triangle_gowers_bound {p : ℕ} [Fact p.Prime] {θ : PlaneIndex} {z : ℤ}
    (hz : 100 ≤ z) (hθ : ParameterBox θ z) (hp : determinantBound z < (p : ℤ))
    (i j₁ j₂ : Fin 6) (js : List (Fin 6)) (hlen : js.length = 3)
    (hpair : j₁ ≠ j₂) (hi : i ∉ j₁ :: j₂ :: js)
    (f : ZMod p → ℂ) (g : Fin 6 → ZMod p → ℂ)
    {B G : ℝ} (hB : 0 < B) (hg : ∀ j u, ‖g j u‖ ≤ B)
    (hG : 0 ≤ G) (hf : gowersCubeMoment 5 f ≤ G ^ 32)
    {E F : Finset (ZMod p)} (hE : E.Nonempty) (hF : F.Nonempty) (s t : ZMod p) :
    ‖meanC (fun x : ZMod p × ZMod p =>
      triangleCutoff E (x.1 - s) * triangleCutoff F (x.2 - t) *
        (f ((integralRowMod θ p i).eval x.1 x.2) *
          ((j₁ :: j₂ :: js).map fun j => g j ((integralRowMod θ p j).eval x.1 x.2)).prod))‖ ≤
      B ^ 5 * G := by
  let w : Fin 6 → BoundedAffineWeight (ZMod p) := fun j =>
    ⟨integralRowDirection hz hθ hp j, (integralRowMod θ p j).constant,
      fun u => g j u / (B : ℂ), fun u => by
        rw [norm_div, Complex.norm_of_nonneg hB.le]
        exact (div_le_iff₀ hB).mpr (by simpa only [one_mul] using hg j u)⟩
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have heval (j : Fin 6) (x : ZMod p × ZMod p) :
      (w j).eval x = g j ((integralRowMod θ p j).eval x.1 x.2) / (B : ℂ) := by
    simp only [w, BoundedAffineWeight.eval, integralRowDirection_eval]
  have hprod (L : List (Fin 6)) (x : ZMod p × ZMod p) :
      affineWeightProduct x (L.map w) =
        (L.map fun j => g j ((integralRowMod θ p j).eval x.1 x.2)).prod / (B : ℂ) ^ L.length := by
    induction L with
    | nil => simp [affineWeightProduct]
    | cons j L ih =>
      simp only [List.map_cons, List.prod_cons, affineWeightProduct, heval, ih, List.length_cons, pow_succ']
      rw [div_mul_div_comm]
  have hdet1 : (w j₁).dir.a * (w j₂).dir.b - (w j₁).dir.b * (w j₂).dir.a ≠ 0 :=
    integralRowDirection_independent hz hθ hp hpair
  have hdet2 : ∀ v ∈ w j₁ :: w j₂ :: js.map w,
      v.dir.a * (integralRowDirection hz hθ hp i).b -
        v.dir.b * (integralRowDirection hz hθ hp i).a ≠ 0 := by
    intro v hv
    change v ∈ (j₁ :: j₂ :: js).map w at hv
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
    exact integralRowDirection_independent hz hθ hp (fun h : j = i => hi (h ▸ hj))
  have htarget (x : ZMod p × ZMod p) :
      f (linearRow (integralRowDirection hz hθ hp i).a (integralRowDirection hz hθ hp i).b x +
        (integralRowMod θ p i).constant) = f ((integralRowMod θ p i).eval x.1 x.2) := by
    rw [integralRowDirection_eval]
  let M := fun x : ZMod p × ZMod p =>
    triangleCutoff E (x.1 - s) * triangleCutoff F (x.2 - t) *
      (f ((integralRowMod θ p i).eval x.1 x.2) * affineWeightProduct x ((j₁ :: j₂ :: js).map w))
  have hbound : ‖meanC M‖ ≤ G := by
    unfold M
    simpa only [htarget, List.map_cons] using
      prime_triangle_weights_gowers_bound (w j₁) (w j₂) (js.map w) (by simpa using hlen) hdet1
        (integralRowDirection hz hθ hp i) (integralRowMod θ p i).constant f hdet2 hE hF s t hG hf
  have heq (x : ZMod p × ZMod p) :
      triangleCutoff E (x.1 - s) * triangleCutoff F (x.2 - t) *
        (f ((integralRowMod θ p i).eval x.1 x.2) *
          ((j₁ :: j₂ :: js).map fun j => g j ((integralRowMod θ p j).eval x.1 x.2)).prod) =
        (B : ℂ) ^ 5 * M x := by
    dsimp only [M]
    rw [hprod, show (j₁ :: j₂ :: js).length = 5 by simp [hlen]]
    field_simp [hBc] <;> ring
  simp_rw [heq, meanC_mul_left, norm_mul, norm_pow, Complex.norm_of_nonneg hB.le]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

end Jsp000881
