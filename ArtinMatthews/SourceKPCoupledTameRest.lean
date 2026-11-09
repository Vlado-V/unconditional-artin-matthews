module

public import ArtinMatthews.SourceKPLocalRestSection
public import ArtinMatthews.SourceKPProjectiveSections


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact section on a tame local Weyl-upper fiber.
Only the genuine compact condition at the place enters these formulas. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (s : ℂ)

local notation "L" => P.adicCompletion K
local notation "G" => SourceKPAdelicProjective K hζ
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ s
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "F₀" => sourceKPAdelicCompactSection K hζ s
local notation "σ₀" => sourceKPAdelicLocalBorelRepresentation K hζ P s
local notation "ν₀" => sourceKPFiniteVal K P

def sourceKPCoupledTameRestValue (r : G) (x : L) : V :=
  (F₀).val (ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) * r)

def sourceKPCoupledTameRestKernel (r : G) (x : L) : ℂ :=
  (sourceKPCoupledTameRestValue K hζ P s r x).val 1

theorem sourceKPCoupledTameRest_factor
    (h6 : (6 : 𝓞 K) ∉ P.asIdeal) (r : SourceKPAdelicProjective K hζ)
    (hr : sourceKPAdelicLocalBase K hζ P r = 1)
    (b : SourceFiniteKPProjectiveBorel K hζ P) (k : SourceFiniteKP2Integral K P) :
    (F₀).val (ι₀ (b.val * sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k) * r) =
      σ₀ b ((F₀).val r) := by
  let q := sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k
  have hc := sourceKPAdelicLocalProjective_commute_of_base_one K hζ P q r hr
  calc
    _ = (F₀).val (ι₀ b.val * (ι₀ q * r)) := by rw [map_mul, mul_assoc]
    _ = σ₀ b ((F₀).val (ι₀ q * r)) :=
      sourceAlgebraicInducedSpace_covariant _ _ F₀ (sourceKPAdelicLocalBorel K hζ P b) _
    _ = σ₀ b ((F₀).val (r * ι₀ q)) := congrArg (fun a => σ₀ b ((F₀).val a)) hc.eq
    _ = _ := congrArg (σ₀ b) (sourceKPAdelicCompactSection_right_local K hζ P h6 s r k)

theorem sourceKPCoupledTameRest_unit_fixed
    (h6 : (6 : 𝓞 K) ∉ P.asIdeal) (r : SourceKPAdelicProjective K hζ)
    (hr : sourceKPAdelicLocalBase K hζ P r = 1) :
    (F₀).val r ∈ sourceKPLocalUnitFixed K hζ P s := by
  intro u hu
  let d := sourceFiniteKPProjectiveBorelDiagonal K hζ P u
  let k : SourceFiniteKP2Integral K P := ⟨sourceGL2Diagonal u, sourceKPIntegralMatrix_diagonal ν₀ u hu⟩
  have hk : sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k = d.val :=
    congrArg (sourceFiniteKP2ProjectiveMk K hζ P) (sourceFiniteKP2CompactSection_diagonal K hζ P h6 u hu)
  have hc := sourceKPAdelicLocalProjective_commute_of_base_one K hζ P d.val r hr
  calc
    σ₀ d ((F₀).val r) = (F₀).val (ι₀ d.val * r) :=
      (sourceAlgebraicInducedSpace_covariant _ _ F₀ (sourceKPAdelicLocalBorel K hζ P d) r).symm
    _ = (F₀).val (r * ι₀ d.val) := congrArg (F₀).val hc.eq
    _ = (F₀).val (r * ι₀ (sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k)) :=
      congrArg (fun q => (F₀).val (r * ι₀ q)) hk.symm
    _ = (F₀).val r := sourceKPAdelicCompactSection_right_local K hζ P h6 s r k

theorem sourceKPCoupledTameRest_value_integral_input
    (h6 : (6 : 𝓞 K) ∉ P.asIdeal) (r : SourceKPAdelicProjective K hζ)
    (hr : sourceKPAdelicLocalBase K hζ P r = 1) (x : L) (hx : ν₀ x ≤ 1) :
    sourceKPCoupledTameRestValue K hζ P s r x = (F₀).val r := by
  let w : SourceFiniteKP2Integral K P := ⟨sourceGL2Weyl, sourceKPIntegralMatrix_weyl ν₀⟩
  let n : SourceFiniteKP2Integral K P := ⟨sourceGL2Upper x, sourceKPIntegralMatrix_upper ν₀ x hx⟩
  let κ := sourceFiniteKP2ProjectiveCompactSection K hζ P h6
  have hw : κ w = l₀ sourceGL2Weyl := congrArg (sourceFiniteKP2ProjectiveMk K hζ P)
    (sourceFiniteKP2CompactSection_weyl K hζ P h6)
  have hn : κ n = l₀ (sourceGL2Upper x) := congrArg (sourceFiniteKP2ProjectiveMk K hζ P)
    (sourceFiniteKP2CompactSection_upper K hζ P h6 x hx)
  unfold sourceKPCoupledTameRestValue
  rw [← hw, ← hn, ← map_mul κ]
  have hc := sourceKPAdelicLocalProjective_commute_of_base_one K hζ P (κ (w*n)) r hr
  rw [hc.eq]
  exact sourceKPAdelicCompactSection_right_local K hζ P h6 s r (w*n)

theorem sourceKPCoupledTameRest_value_open
    (h6 : (6 : 𝓞 K) ∉ P.asIdeal) (r : SourceKPAdelicProjective K hζ)
    (hr : sourceKPAdelicLocalBase K hζ P r = 1) (x : Lˣ) (hx : ν₀ ((x : L)⁻¹) ≤ 1) :
    sourceKPCoupledTameRestValue K hζ P s r (x : L) =
      σ₀ (sourceFiniteKPProjectiveBorelDiagonal K hζ P (sourceBruhatDiagonal x)) ((F₀).val r) := by
  let b := sourceFiniteKPProjectiveBorelUpper K hζ P ((x : L)⁻¹)
  let d := sourceFiniteKPProjectiveBorelDiagonal K hζ P (sourceBruhatDiagonal x)
  let k : SourceFiniteKP2Integral K P := ⟨sourceGL2Lower ((x : L)⁻¹),
    sourceKPIntegralMatrix_lower ν₀ _ hx⟩
  have hk : sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k = l₀ (sourceGL2Lower ((x : L)⁻¹)) :=
    sourceFiniteKP2ProjectiveCompactSection_lower K hζ P h6 _ hx
  have he : l₀ sourceGL2Weyl * l₀ (sourceGL2Upper (x : L)) =
      (b*d).val * sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k := by
    rw [hk]
    exact sourceFiniteKP2ProjectiveLift_weyl_upper K hζ P x
  unfold sourceKPCoupledTameRestValue
  rw [he, sourceKPCoupledTameRest_factor K hζ P s h6 r hr (b*d) k,
    map_mul, Module.End.mul_apply]
  exact sourceKPAdelicLocalBorelRepresentation_upper K hζ P s _ _

end
end ArtinMatthews
