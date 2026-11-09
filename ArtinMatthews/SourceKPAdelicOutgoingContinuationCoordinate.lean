module

public import ArtinMatthews.SourceKPAdelicOutgoingContinuationScalar
public import ArtinMatthews.SourceKPAdelicFlatTorus


set_option backward.privateInPublic true
@[expose] public section

/-! Regularization at the actual scattering pole preserves all exact
inducing, Borel and deep-level identities of the measured coordinates. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "G" => SourceKPAdelicProjective K hζ
local notation "B" => sourceKPAdelicCoveringBorel K hζ
local notation "T" => sourceKPAdelicCoveringTorus K hζ
local notation "H" => sourceKPAdelicTorusInducingSubgroup K hζ
local notation "D" => sourceKPAdelicDeepCompact K hζ
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "δ" => sourceKPAdelicBorelModularHalf K hζ
local notation "d₀" => sourceKPAdelicBorelTorusInclusion K hζ
local notation "p" => sourceKPAdelicBorelTorusProjection K hζ
local notation "χ" => sourceKPAdelicTorusInducingCharacter K hζ
local notation "O" => sourceKPAdelicOutgoingSection K hζ
local notation "R" => sourceKPAdelicOutgoingRegularizedScalar K hζ

def sourceKPAdelicOutgoingRegularizedCoordinate (s : ℂ) (g : G) (t : T) : ℂ :=
  (δ (d₀ t))⁻¹ * R s (t.val*g)

local notation "C" => sourceKPAdelicOutgoingRegularizedCoordinate K hζ

theorem sourceKPAdelicOutgoingRegularizedCoordinate_one (s : ℂ) (g : G) :
    C s g 1 = R s g := by
  rw [sourceKPAdelicOutgoingRegularizedCoordinate,map_one d₀,map_one δ,inv_one,one_mul]
  change R s (1*g) = R s g
  rw [one_mul]

theorem sourceKPAdelicOutgoingRegularizedCoordinate_analyticOnNhd (g : G) (t : T) :
    AnalyticOnNhd ℂ (fun s => C s g t) {s : ℂ | 0 < s.re} := by
  intro s hs
  exact analyticAt_const.mul
    (sourceKPAdelicOutgoingRegularizedScalar_analyticOnNhd K hζ (t.val*g) s hs)

theorem sourceKPAdelicOutgoingRegularizedCoordinate_initial (s : ℂ)
    (hs : SourceKPAdelicOutgoingInitial K s) (g : G) (t : T) :
    C s g t = (s-1/6)*((O s).val g).val t := by
  rw [sourceKPAdelicOutgoingRegularizedCoordinate,
    sourceKPAdelicOutgoingRegularizedScalar_initial K hζ s hs (t.val*g),
    sourceKPAdelicOutgoingSection_trace_coordinate K hζ s g t]
  ring

theorem sourceKPAdelicOutgoingInducingCharacter_analyticAt (h : H) (s : ℂ) :
    AnalyticAt ℂ (fun z => (χ (-z) h : ℂ)) s := by
  let c : ℂ := (Real.log (sourceKPIdeleAbsoluteNorm K (sourceKPAdelicTorusIdele K hζ h.val)) : ℂ)
  have he : (fun z : ℂ => (χ (-z) h : ℂ)) = fun z => (χ 0 h : ℂ)*Complex.exp ((-z)*c) := by
    funext z
    rw [sourceKPAdelicTorusInducingCharacter_flat K hζ (-z) h,Units.val_mul,sourceKPIdeleComplexNorm_coe]
  rw [he]
  have hf : AnalyticAt ℂ (fun z : ℂ => (-z)*c) s := analyticAt_id.neg.mul analyticAt_const
  exact analyticAt_const.mul hf.cexp'

theorem sourceKPAdelicOutgoingRegularizedCoordinate_inducing (s : ℂ) (hs : 0 < s.re)
    (g : G) (h : H) (t : T) : C s g (h.val*t) = (χ (-s) h : ℂ)*C s g t := by
  apply sourceKPAdelicOutgoingAnalytic_eqOn_of_initial K
    (sourceKPAdelicOutgoingRegularizedCoordinate_analyticOnNhd K hζ g (h.val*t))
    (fun z hz => (sourceKPAdelicOutgoingInducingCharacter_analyticAt K hζ h z).mul
      (sourceKPAdelicOutgoingRegularizedCoordinate_analyticOnNhd K hζ g t z hz)) _ hs
  intro z hz
  change C z g (h.val*t) = (χ (-z) h : ℂ)*C z g t
  have he := ((O z).val g).property h t
  change ((O z).val g).val (h.val*t) = (χ (-z) h : ℂ)*((O z).val g).val t at he
  rw [sourceKPAdelicOutgoingRegularizedCoordinate_initial K hζ z hz g (h.val*t),
    sourceKPAdelicOutgoingRegularizedCoordinate_initial K hζ z hz g t,he]
  ring

theorem sourceKPAdelicOutgoingRegularizedCoordinate_borel (s : ℂ) (hs : 0 < s.re)
    (b : B) (g : G) (t : T) : C s (b.val*g) t = δ b*C s g (t*p b) := by
  apply sourceKPAdelicOutgoingAnalytic_eqOn_of_initial K
    (sourceKPAdelicOutgoingRegularizedCoordinate_analyticOnNhd K hζ (b.val*g) t)
    (fun z hz => analyticAt_const.mul
      (sourceKPAdelicOutgoingRegularizedCoordinate_analyticOnNhd K hζ g (t*p b) z hz)) _ hs
  intro z hz
  change C z (b.val*g) t = δ b*C z g (t*p b)
  have he := congrArg (fun v : V (-z) => v.val t) ((O z).property b g)
  change ((O z).val (b.val*g)).val t = δ b*((O z).val g).val (t*p b) at he
  rw [sourceKPAdelicOutgoingRegularizedCoordinate_initial K hζ z hz (b.val*g) t,
    sourceKPAdelicOutgoingRegularizedCoordinate_initial K hζ z hz g (t*p b),he]
  ring

theorem sourceKPAdelicOutgoingRegularizedCoordinate_deep_right (s : ℂ) (hs : 0 < s.re)
    (g : G) (k : D) (t : T) : C s (g*k.val) t = C s g t := by
  apply sourceKPAdelicOutgoingAnalytic_eqOn_of_initial K
    (sourceKPAdelicOutgoingRegularizedCoordinate_analyticOnNhd K hζ (g*k.val) t)
    (sourceKPAdelicOutgoingRegularizedCoordinate_analyticOnNhd K hζ g t) _ hs
  intro z hz
  rw [sourceKPAdelicOutgoingRegularizedCoordinate_initial K hζ z hz (g*k.val) t,
    sourceKPAdelicOutgoingRegularizedCoordinate_initial K hζ z hz g t]
  have he := sourceKPAdelicOutgoingValue_deep_right K hζ z g k
  exact congrArg (fun v : V (-z) => (z-1/6)*v.val t) he

end
end ArtinMatthews
