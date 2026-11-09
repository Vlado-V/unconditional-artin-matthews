module

public import ArtinMatthews.SourceKPAdelicOutgoingContinuationCoordinate


set_option backward.privateInPublic true
@[expose] public section

/-! The regularized measured outgoing family is an actual induced
section on the positive half-plane. The value at the scattering pole
is the coordinatewise residue of its actual meromorphic continuation. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Filter
open scoped NumberField AdeleRing Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "G" => SourceKPAdelicProjective K hζ
local notation "T" => sourceKPAdelicCoveringTorus K hζ
local notation "D" => sourceKPAdelicDeepCompact K hζ
local notation "O" => sourceKPAdelicOutgoingSection K hζ
local notation "δ" => sourceKPAdelicBorelModularHalf K hζ
local notation "d₀" => sourceKPAdelicBorelTorusInclusion K hζ
local notation "C" => sourceKPAdelicOutgoingRegularizedCoordinate K hζ
local notation "M" => sourceKPAdelicOutgoingContinuationScalar K hζ

def sourceKPAdelicOutgoingRegularizedSection (s : ℂ) (hs : 0 < s.re) :
    SourceKPAdelicPrincipalSeries K hζ (-s) :=
  ⟨fun g => ⟨C s g, fun h t => sourceKPAdelicOutgoingRegularizedCoordinate_inducing K hζ s hs g h t⟩,
    fun b g => Subtype.ext (funext (sourceKPAdelicOutgoingRegularizedCoordinate_borel K hζ s hs b g))⟩

local notation "R" => sourceKPAdelicOutgoingRegularizedSection K hζ

theorem sourceKPAdelicOutgoingRegularizedSection_coordinate (s : ℂ) (hs : 0 < s.re)
    (g : G) (t : T) : ((R s hs).val g).val t = C s g t := rfl

theorem sourceKPAdelicOutgoingRegularizedSection_initial (s : ℂ)
    (hs : SourceKPAdelicOutgoingInitial K s) :
    R s (zero_lt_one.trans_le (sourceKPAdelicOutgoingInitial_re_one_le K hs)) =
      (s-1/6) • O s := by
  apply Subtype.ext
  funext g
  apply Subtype.ext
  funext t
  exact sourceKPAdelicOutgoingRegularizedCoordinate_initial K hζ s hs g t

theorem sourceKPAdelicOutgoingRegularizedSection_right (s : ℂ) (hs : 0 < s.re) (k : D) :
    sourceKPAdelicPrincipalSeriesRepresentation K hζ (-s) k.val (R s hs) = R s hs := by
  apply Subtype.ext
  funext g
  apply Subtype.ext
  funext t
  exact sourceKPAdelicOutgoingRegularizedCoordinate_deep_right K hζ s hs g k t

def sourceKPAdelicOutgoingContinuationCoordinate (s : ℂ) (g : G) (t : T) : ℂ :=
  (δ (d₀ t))⁻¹ * M s (t.val*g)

local notation "Q" => sourceKPAdelicOutgoingContinuationCoordinate K hζ

theorem sourceKPAdelicOutgoingContinuationCoordinate_initial (s : ℂ)
    (hs : SourceKPAdelicOutgoingInitial K s) (g : G) (t : T) :
    Q s g t = ((O s).val g).val t := by
  rw [sourceKPAdelicOutgoingContinuationCoordinate,
    sourceKPAdelicOutgoingContinuationScalar_initial K hζ s hs (t.val*g),
    sourceKPAdelicOutgoingSection_trace_coordinate K hζ s g t]

theorem sourceKPAdelicOutgoingContinuationCoordinate_meromorphicOn (g : G) (t : T) :
    MeromorphicOn (fun s => Q s g t) {s : ℂ | 0 < s.re} := by
  intro s hs
  have h : AnalyticAt ℂ (fun _ : ℂ => (δ (d₀ t))⁻¹) s := analyticAt_const
  exact h.meromorphicAt.mul
    (sourceKPAdelicOutgoingContinuationScalar_meromorphicOn K hζ (t.val*g) s hs)

def sourceKPAdelicOutgoingExceptionalSection : SourceKPAdelicPrincipalSeries K hζ (-(1/6 : ℂ)) :=
  R (1/6) (by norm_num)

theorem sourceKPAdelicOutgoingExceptionalSection_residue_tendsto (g : G) (t : T) :
    Tendsto (fun s => (s-1/6)*Q s g t) (𝓝[≠] (1/6 : ℂ))
      (𝓝 (((sourceKPAdelicOutgoingExceptionalSection K hζ).val g).val t)) := by
  refine (tendsto_const_nhds.mul
    (sourceKPAdelicOutgoingContinuationScalar_residue_tendsto K hζ (t.val*g))).congr' ?_
  exact Eventually.of_forall fun s => by
    unfold sourceKPAdelicOutgoingContinuationCoordinate
    ring

end
end ArtinMatthews
