module

public import ArtinMatthews.SpectralCompactEigenbasis
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Finite bounded spectral windows, with multiplicities, from actual compactness.
This proves qualitative finiteness only; it does not assert a Weyl counting rate. -/
namespace ArtinMatthews.SpectralCompact
open Set
open scoped InnerProductSpace
noncomputable section

universe u v
variable {H : Type u} {ι : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem orthonormal_eigenvalue_le_image_distance (T : H →L[ℂ] H)
    (v : ι → H) (hv : Orthonormal ℂ v) (μ : ι → ℂ)
    (he : ∀ i, T (v i) = μ i • v i) {i j : ι} (hij : i ≠ j) :
    ‖μ i‖ ≤ dist (T (v i)) (T (v j)) := by
  have hi : inner ℂ (v i) (T (v i) - T (v j)) = μ i := by
    rw [inner_sub_right, he i, he j, inner_smul_right, inner_smul_right,
      hv.inner_eq_zero hij, inner_self_eq_norm_sq_to_K,
      hv.norm_eq_one]
    simp
  have hb := norm_inner_le_norm (𝕜 := ℂ) (v i) (T (v i) - T (v j))
  rw [hi, hv.norm_eq_one, one_mul, ← dist_eq_norm] at hb
  exact hb

/-- A compact operator has only finitely many vectors of an orthonormal eigenfamily
whose eigenvalue norm stays above a fixed positive threshold, counting multiplicity. -/
theorem orthonormal_eigenvalue_cutoff_finite (T : H →L[ℂ] H)
    (hT : IsCompactOperator T) (v : ι → H) (hv : Orthonormal ℂ v) (μ : ι → ℂ)
    (he : ∀ i, T (v i) = μ i • v i) {ε : ℝ} (hε : 0 < ε) :
    {i : ι | ε ≤ ‖μ i‖}.Finite := by
  classical
  obtain ⟨K, hK, hTK⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded (ε / 3) (by positivity)
  let S := {i : ι | ε ≤ ‖μ i‖}
  have hm (i : S) : T (v i.val) ∈ K :=
    hTK ⟨v i.val, by simp [Metric.mem_closedBall, hv.norm_eq_one], rfl⟩
  have hchoose (i : S) : ∃ y : t, dist (T (v i.val)) y.val < ε / 3 := by
    obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (hcover (hm i))
    exact ⟨⟨y, hyt⟩, hy⟩
  let c : S → t := fun i => (hchoose i).choose
  have hc (i : S) : dist (T (v i.val)) (c i).val < ε / 3 := (hchoose i).choose_spec
  have hinj : Function.Injective c := by
    intro i j hij
    apply Subtype.ext
    by_contra hn
    have hb := orthonormal_eigenvalue_le_image_distance T v hv μ he hn
    have hd := dist_triangle (T (v i.val)) (c i).val (T (v j.val))
    have hci := hc i
    have hcj := hc j
    rw [← hij, dist_comm (T (v j.val))] at hcj
    have hi : ε ≤ ‖μ i.val‖ := i.property
    linarith
  have : Finite t := ht.to_subtype
  have : Finite S := Finite.of_injective c hinj
  exact Set.toFinite S

end
end ArtinMatthews.SpectralCompact
