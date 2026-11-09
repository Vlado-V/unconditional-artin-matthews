module

public import ArtinMatthews.SourceKPLocalReceiverUnits
public import Mathlib.RepresentationTheory.Intertwining


set_option backward.privateInPublic true
@[expose] public section

/-! The three-basis map intertwines the complete actual local Borel.
The global fixed vector is constructed from the original unit section. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀) (s : ℂ)
    (v : sourceKPLocalUnitFixed K hζ P.val s)

local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ s
local notation "B" => SourceFiniteKPProjectiveBorel K hζ P.val
local notation "ρ" => sourceKPTameParametricBorelRepresentation K hζ P.val h₆ π₀ hπ₀ s
local notation "σ" => sourceKPAdelicLocalBorelRepresentation K hζ P.val s
local notation "R" => sourceKPLocalReceiver K hζ P.val π₀ s v.val

theorem sourceKPLocalReceiverSubgroup_diagonal (y : (P.val.adicCompletion K)ˣ) :
    sourceFiniteKPProjectiveBorelDiagonal K hζ P.val y ∈
      sourceKPLocalReceiverSubgroup K hζ S₀ P s v.val := by
  let j := sourceKPValuationOrder (sourceKPFiniteVal K P.val) y
  let u := sourceKPUnitPart (sourceKPFiniteVal K P.val) π₀ y
  let z := sourceFiniteKPHilbert K hζ P.val (π₀^j) u ^ 2
  have hu : sourceKPFiniteVal K P.val (u : P.val.adicCompletion K) = 1 :=
    sourceKPUnitPart_valuation (sourceKPFiniteVal K P.val) π₀ hπ₀ y
  have hy : π₀^j*u = y := sourceKPUnitPart_factor (sourceKPFiniteVal K P.val) π₀ y
  have hd := sourceKPLocalReceiverSubgroup_uniformizer_power K hζ S₀ P s v.val j
  have hunit := sourceKPLocalReceiverSubgroup_unit K hζ S₀ P s v u hu
  have hcenter := sourceKPLocalReceiverSubgroup_center K hζ S₀ P s v.val z
  have h := (sourceKPLocalReceiverSubgroup K hζ S₀ P s v.val).mul_mem
    ((sourceKPLocalReceiverSubgroup K hζ S₀ P s v.val).inv_mem hcenter)
    ((sourceKPLocalReceiverSubgroup K hζ S₀ P s v.val).mul_mem hd hunit)
  have he : (sourceFiniteKPProjectiveBorelCenter K hζ P.val z)⁻¹ *
      (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val (π₀^j) *
        sourceFiniteKPProjectiveBorelDiagonal K hζ P.val u) =
      sourceFiniteKPProjectiveBorelDiagonal K hζ P.val y := by
    rw [sourceKPLocalBorelDiagonal_mul, hy, inv_mul_cancel_left]
  rwa [he] at h

theorem sourceKPLocalReceiverSubgroup_all (b : B) :
    b ∈ sourceKPLocalReceiverSubgroup K hζ S₀ P s v.val := by
  obtain ⟨z, x, y, hb⟩ := sourceFiniteKPProjectiveBorel_factor K hζ P.val b
  have he : b = sourceFiniteKPProjectiveBorelCenter K hζ P.val z *
      sourceFiniteKPProjectiveBorelUpper K hζ P.val x *
        sourceFiniteKPProjectiveBorelDiagonal K hζ P.val y := Subtype.ext hb
  rw [he]
  exact (sourceKPLocalReceiverSubgroup K hζ S₀ P s v.val).mul_mem
    ((sourceKPLocalReceiverSubgroup K hζ S₀ P s v.val).mul_mem
      (sourceKPLocalReceiverSubgroup_center K hζ S₀ P s v.val z)
      (sourceKPLocalReceiverSubgroup_upper K hζ S₀ P s v.val x))
    (sourceKPLocalReceiverSubgroup_diagonal K hζ S₀ P s v y)

def sourceKPLocalReceiverIntertwining : Representation.IntertwiningMap ρ σ where
  toLinearMap := R
  isIntertwining' b := by
    apply LinearMap.ext
    intro f
    exact sourceKPLocalReceiverSubgroup_all K hζ S₀ P s v b f

theorem sourceKPLocalReceiverIntertwining_apply (f : ZMod 3 → ℂ) :
    sourceKPLocalReceiverIntertwining K hζ S₀ P s v f = R f := rfl

theorem sourceKPLocalReceiverIntertwining_zero :
    sourceKPLocalReceiverIntertwining K hζ S₀ P s v (sourceJacquetBasis 0) = v.val :=
  sourceKPLocalReceiver_zero K hζ P.val π₀ s v.val

def sourceKPLocalSphericalFixedVector : sourceKPLocalUnitFixed K hζ P.val s :=
  ⟨sourceKPAdelicUnitSphericalVector K hζ s, sourceKPLocalUnitFixed_spherical K hζ P.val h₆ s⟩

def sourceKPLocalSphericalReceiver : Representation.IntertwiningMap ρ σ :=
  sourceKPLocalReceiverIntertwining K hζ S₀ P s (sourceKPLocalSphericalFixedVector K hζ S₀ P s)

theorem sourceKPLocalSphericalReceiver_zero :
    sourceKPLocalSphericalReceiver K hζ S₀ P s (sourceJacquetBasis 0) =
      sourceKPAdelicUnitSphericalVector K hζ s :=
  sourceKPLocalReceiverIntertwining_zero K hζ S₀ P s (sourceKPLocalSphericalFixedVector K hζ S₀ P s)

theorem sourceKPLocalSphericalReceiver_ne_zero :
    sourceKPLocalSphericalReceiver K hζ S₀ P s ≠ 0 := by
  intro h
  have he := congrArg (fun f : Representation.IntertwiningMap ρ σ => f (sourceJacquetBasis 0)) h
  rw [sourceKPLocalSphericalReceiver_zero] at he
  exact sourceKPAdelicUnitSphericalVector_ne_zero K hζ s he

end
end ArtinMatthews
