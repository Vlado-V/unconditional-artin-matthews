module

public import ArtinMatthews.SourceKPJacquetDiagonalScale
public import ArtinMatthews.SourceKPLocalCompactBorelOrbit


set_option backward.privateInPublic true
@[expose] public section

/-! The normalized diagonal keeps the genuine cubic multiplier.
At the negative residue parameter its action is constant on cube classes. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain SourcePhysical
open scoped NumberField SourcePhysical Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "d₀" => sourceFiniteKPProjectiveBorelDiagonal K hζ P
local notation "z₀" => sourceFiniteKPProjectiveBorelCenter K hζ P

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) V)

def SourceKPJacquetNegativeCubeLaw : Prop :=
  ∀ (u : Lˣ) (v : V), ρ (d₀ (u ^ 3)) v = (↑(‖((u ^ 3 : Lˣ) : L)‖ ^ (1 / 3 : ℝ)) : ℂ) • v

theorem sourceKPJacquet_unitCube_of_negativeCubeLaw (hCube : SourceKPJacquetNegativeCubeLaw K hζ P ρ)
    (u : Lˣ) (hu : sourceLocalValuation K P ((u ^ 3 : Lˣ) : L) = 1) (v : V) :
    ρ (d₀ (u ^ 3)) v = v := by
  rw [hCube, Valued.toNormedField.norm_eq_one_iff.mpr hu, Real.one_rpow, Complex.ofReal_one, one_smul]

def sourceKPJacquetFlatDiagonal (u : Lˣ) : V →ₗ[ℂ] V :=
  (↑(‖(u : L)‖ ^ (-(1 / 3) : ℝ)) : ℂ) • ρ (d₀ u)

local notation "D" => sourceKPJacquetFlatDiagonal K hζ P ρ

theorem sourceKPJacquet_diagonal_eq_smul_flat (u : Lˣ) (v : V) :
    ρ (d₀ u) v = (↑(‖(u : L)‖ ^ (1 / 3 : ℝ)) : ℂ) • D u v := by
  change _ = (↑(‖(u : L)‖ ^ (1 / 3 : ℝ)) : ℂ) •
    ((↑(‖(u : L)‖ ^ (-(1 / 3) : ℝ)) : ℂ) • ρ (d₀ u) v)
  rw [smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add (norm_pos_iff.mpr u.ne_zero), add_neg_cancel,
    Real.rpow_zero, Complex.ofReal_one, one_smul]

theorem sourceKPJacquetFlatDiagonal_mul (u v : Lˣ) :
    D u * D v = ρ (z₀ (sourceFiniteKPHilbert K hζ P u v ^ 2)) * D (u * v) := by
  apply LinearMap.ext
  intro x
  change (↑(‖(u : L)‖ ^ (-(1 / 3) : ℝ)) : ℂ) •
      ρ (d₀ u) ((↑(‖(v : L)‖ ^ (-(1 / 3) : ℝ)) : ℂ) • ρ (d₀ v) x) =
    ρ (z₀ (sourceFiniteKPHilbert K hζ P u v ^ 2))
      ((↑(‖((u * v : Lˣ) : L)‖ ^ (-(1 / 3) : ℝ)) : ℂ) • ρ (d₀ (u * v)) x)
  rw [map_smul, smul_smul, ← Complex.ofReal_mul, ← Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
    ← norm_mul, ← Units.val_mul, map_smul, ← Module.End.mul_apply, ← map_mul,
    sourceKPLocalBorelDiagonal_mul, map_mul, Module.End.mul_apply]

theorem sourceKPJacquetFlatDiagonal_cubeClass (hCube : SourceKPJacquetNegativeCubeLaw K hζ P ρ)
    (u : Lˣ) : D u = D ((QuotientGroup.mk u : SourceKPLocalCompactCubeClasses K P).out) := by
  let q : SourceKPLocalCompactCubeClasses K P := QuotientGroup.mk u
  let a := q.out
  have hq : (QuotientGroup.mk a : SourceKPLocalCompactCubeClasses K P) = QuotientGroup.mk u :=
    QuotientGroup.out_eq' q
  obtain ⟨b, hb⟩ := QuotientGroup.eq.mp hq
  change b ^ (3 : ℕ) = a⁻¹ * u at hb
  have he : a * b ^ 3 = u := by rw [hb, mul_inv_cancel_left]
  have hB : D (b ^ 3) = 1 := by
    apply LinearMap.ext
    intro v
    change (↑(‖((b ^ 3 : Lˣ) : L)‖ ^ (-(1 / 3) : ℝ)) : ℂ) • ρ (d₀ (b ^ 3)) v = v
    rw [hCube, smul_smul, ← Complex.ofReal_mul,
      ← Real.rpow_add (norm_pos_iff.mpr (b ^ 3).ne_zero), neg_add_cancel,
      Real.rpow_zero, Complex.ofReal_one, one_smul]
  have hc := sourceKPJacquetFlatDiagonal_mul K hζ P ρ a (b ^ 3)
  have h1 : z₀ (1 : rootsOfUnity 3 L) = 1 := by
    apply Subtype.ext
    exact map_one _
  rw [sourceFiniteKPHilbert_cube_right K hζ P, one_pow, h1, map_one, one_mul, hB, mul_one, he] at hc
  exact hc.symm

theorem sourceKPJacquetFlatDiagonal_norm_bound {ι : Type*} [Fintype ι] (e : V ≃ₗ[ℂ] (ι → ℂ))
    (hCube : SourceKPJacquetNegativeCubeLaw K hζ P ρ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (u : Lˣ) (v : V), ‖e (D u v)‖ ≤ A * ‖e v‖ := by
  let Q := SourceKPLocalCompactCubeClasses K P
  let : Finite Q := sourceKPLocalCompactCubeClasses_finite K P
  let : Fintype Q := Fintype.ofFinite Q
  let F (q : Q) : (ι → ℂ) →L[ℂ] (ι → ℂ) := LinearMap.toContinuousLinearMap
    (e.toLinearMap.comp ((D q.out).comp e.symm.toLinearMap))
  let A := 1 + ∑ q : Q, ‖F q‖
  have hsum : 0 ≤ ∑ q : Q, ‖F q‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨A, by dsimp only [A]; linarith, fun u v => ?_⟩
  let q : Q := QuotientGroup.mk u
  have hq : ‖F q‖ ≤ A := by
    have h := Finset.single_le_sum (f := fun q : Q => ‖F q‖)
      (fun q _ => norm_nonneg (F q)) (Finset.mem_univ q)
    dsimp only [A]
    linarith
  rw [sourceKPJacquetFlatDiagonal_cubeClass K hζ P ρ hCube u]
  have hF : F q (e v) = e (D q.out v) := by
    change e (D q.out (e.symm (e v))) = _
    rw [e.symm_apply_apply]
  rw [← hF]
  exact (ContinuousLinearMap.le_opNorm (F q) (e v)).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg _))

theorem sourceKPJacquet_diagonal_Haar_factor (u : Lˣ) (v : V) :
    (‖(u : L)‖ : ℂ) • ρ (d₀ u⁻¹) v = (↑(‖(u : L)‖ ^ (2 / 3 : ℝ)) : ℂ) • D u⁻¹ v := by
  have hN : 0 < ‖(u : L)‖ := norm_pos_iff.mpr u.ne_zero
  rw [sourceKPJacquet_diagonal_eq_smul_flat K hζ P ρ, smul_smul, ← Complex.ofReal_mul]
  congr 2
  rw [Units.val_inv_eq_inv_val, norm_inv, ← Real.rpow_neg_eq_inv_rpow]
  conv_lhs => lhs; rw [← Real.rpow_one ‖(u : L)‖]
  rw [← Real.rpow_add hN]
  norm_num

end
end ArtinMatthews
