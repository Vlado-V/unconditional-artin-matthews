module

public import ArtinMatthews.SourceKPLocalReceiverIntegral
public import ArtinMatthews.SourceKPLocalRestSection


set_option backward.privateInPublic true
@[expose] public section

/-! Full and unit-ball local integrals for the literal global section,
with its remaining global factor kept as an algebraic carrier value. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀) (s : ℂ)

local notation "L" => P.val.adicCompletion K
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P.val
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "F₀" => sourceKPAdelicCompactSection K hζ s
local notation "μ₀" => sourceJacquetHaar K P.val

theorem sourceKPLocalRest_integrable (r : SourceKPAdelicProjective K hζ)
    (hr : sourceKPAdelicLocalBase K hζ P.val r = 1)
    (t : sourceKPAdelicCoveringTorus K hζ)
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) :
    Integrable (fun x : L =>
      ((F₀).val (ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) * r)).val t) μ₀ := by
  simp_rw [sourceKPLocalRest_section K hζ S₀ P s r hr]
  exact sourceKPLocalReceiver_integrable K hζ S₀ P s
    (sourceKPLocalRestVector K hζ S₀ P s r hr) t hP hs

theorem sourceKPLocalRest_integral (r : SourceKPAdelicProjective K hζ)
    (hr : sourceKPAdelicLocalBase K hζ P.val r = 1)
    (t : sourceKPAdelicCoveringTorus K hζ)
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) :
    (∫ x : L, ((F₀).val (ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) * r)).val t ∂μ₀) =
      sourceKPUnramifiedScatteringFactor P.val s * ((F₀).val r).val t := by
  simp_rw [sourceKPLocalRest_section K hζ S₀ P s r hr]
  exact sourceKPLocalReceiver_integral K hζ S₀ P s
    (sourceKPLocalRestVector K hζ S₀ P s r hr) t hP hs

theorem sourceKPLocalRest_unit_ball (r : SourceKPAdelicProjective K hζ)
    (hr : sourceKPAdelicLocalBase K hζ P.val r = 1)
    (t : sourceKPAdelicCoveringTorus K hζ) :
    (∫ x : L in sourceLocalBall K P.val 0,
      ((F₀).val (ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) * r)).val t ∂μ₀) =
      ((F₀).val r).val t := by
  simp_rw [sourceKPLocalRest_section K hζ S₀ P s r hr]
  exact sourceKPLocalReceiver_unit_ball K hζ S₀ P s
    (sourceKPLocalRestVector K hζ S₀ P s r hr) t

theorem sourceKPLocalRest_integral_eq_factor_unit_ball (r : SourceKPAdelicProjective K hζ)
    (hr : sourceKPAdelicLocalBase K hζ P.val r = 1)
    (t : sourceKPAdelicCoveringTorus K hζ)
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) :
    (∫ x : L, ((F₀).val (ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) * r)).val t ∂μ₀) =
      sourceKPUnramifiedScatteringFactor P.val s *
        ∫ x : L in sourceLocalBall K P.val 0,
          ((F₀).val (ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) * r)).val t ∂μ₀ := by
  rw [sourceKPLocalRest_integral K hζ S₀ P s r hr t hP hs,
    sourceKPLocalRest_unit_ball K hζ S₀ P s r hr t]

end
end ArtinMatthews
