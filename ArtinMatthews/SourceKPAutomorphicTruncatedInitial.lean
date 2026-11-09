module

public import ArtinMatthews.SourceKPCompactTruncatedForm
public import ArtinMatthews.SourceKPAutomorphicSpectralFamily


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine resolvent agrees with the literal truncated series in its initial region. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter HilbertResolvent
open scoped NumberField MatrixGroups AdeleRing Topology InnerProductSpace
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "V" => SourceKPCompactH1 K hζ
local notation "Vχ" => SourceKPCompactGenuineH1 K hζ
local notation "j" => sourceKPCompactGenuineH1Mass K hζ
local notation "j₀" => sourceKPCompactH1Mass K hζ
local notation "L" => SourceKPAutomorphicL2 K hζ (sourceKPArchHaar K hζ)
local notation "rK" => (InfinitePlace.nrComplexPlaces K : ℝ)

theorem sourceKPCompactTruncated_genuine_mass {T : ℝ} {s : ℂ} (u : V)
    (hu : (j₀ u : Y → ℂ) =ᵐ[μY] sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s) :
    u ∈ sourceKPCompactGenuineH1 K hζ := by
  change j₀ u ∈ sourceKPCompactGenuineL2Subspace K hζ (sourceKPArchHaar K hζ)
  apply (sourceKPCompactGenuineL2Subspace_mem_ae K hζ (sourceKPArchHaar K hζ) (j₀ u)).mpr
  intro z
  have hz := (sourceKPAutomorphicCompactMeasure_center_preserving K hζ z
    (sourceKPArchHaar K hζ)).quasiMeasurePreserving.ae_eq_comp hu
  filter_upwards [hu,hz] with y hy hzy
  calc
    (j₀ u : Y → ℂ) (z • y) =
        sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s (z • y) := hzy
    _ = (sourceKPAdelicCentralComplex K hζ z : ℂ)*
        sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s y :=
      sourceKPAutomorphicCompactTruncatedEisenstein_center K hζ T s z y
    _ = _ := congrArg (fun w => (sourceKPAdelicCentralComplex K hζ z : ℂ)*w) hy.symm

theorem sourceKPAutomorphicTruncatedContinuation_ae_of_memLp {T : ℝ} (hT : 1 ≤ T) {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (hwL : MemLp (sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s) 2 μY) :
    ((sourceKPAutomorphicTruncatedContinuation K hζ hT s : L) : Y → ℂ) =ᵐ[μY]
      sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s := by
  obtain ⟨u,hu,hweak⟩ := sourceKPCompactTruncated_form K hζ hT hs hwL
  let U : Vχ := ⟨u,sourceKPCompactTruncated_genuine_mass K hζ u hu⟩
  let d := sourceKPAutomorphicGenuineDefectL2 K hζ hT s
  let lam := spectralParameter rK s
  have hP : pencil ((j).adjoint.comp j) lam U = -(j).adjoint d := by
    apply ext_inner_left (𝕜 := ℂ)
    intro v
    rw [pencil_adjoint_comp_inner_right,inner_neg_right,(j).adjoint_inner_right]
    have h := hweak v.val
    rw [sourceKPCompactH1Dirichlet,← sourceKPAutomorphicSpectralParameter_eq K s] at h
    have h' : inner ℂ v U-inner ℂ (j v) (j U) =
        lam*inner ℂ (j v) (j U)-inner ℂ (j v) d := by
      simp only [Submodule.coe_inner,sourceKPCompactGenuineH1Mass_coe]
      change inner ℂ v.val u-inner ℂ (j₀ v.val) (j₀ u) =
        spectralParameter rK s*inner ℂ (j₀ v.val) (j₀ u) -
          inner ℂ (j₀ v.val) (sourceKPAutomorphicGenuineDefectL2 K hζ hT s : L)
      rw [sourceKPAutomorphicGenuineDefectL2_coe]
      exact h
    linear_combination h'
  rw [sourceKPAutomorphicTruncatedContinuation_eq_of_pencil K hζ hT hs U hP,
    sourceKPCompactGenuineH1Mass_coe]
  exact hu

end
end ArtinMatthews
