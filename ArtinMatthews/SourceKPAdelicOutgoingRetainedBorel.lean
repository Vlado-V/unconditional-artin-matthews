module

public import ArtinMatthews.SourceKPAdelicOutgoingContinuedCompactCarrier


set_option backward.privateInPublic true
@[expose] public section

/-! The finite all-remainder carrier is stable under the actual
retained Borel action. This is an explicit subrepresentation, and
the actual regularized section has the corresponding covariance. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "Rest" => SourceKPAdelicOutgoingRetainedRest K hζ S
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "R" => sourceKPAdelicOutgoingRegularizedSection K hζ
local notation "ρ" => sourceKPAdelicNormalizedBorelRepresentation K hζ
local notation "Gₛ" => SourceKPLocalCompactProductGroup K hζ S
local notation "Bₛ" => SourceKPLocalCompactProductBorel K hζ S
local notation "Q" => SourceKPLocalCompactProductLabel K hζ S
local notation "L" => sourceKPLocalCompactProductLift K hζ S
local notation "Lᴮ" => sourceKPLocalCompactProductBorelLift K hζ S
local notation "D" => sourceKPLocalCompactProductCubeBorel K hζ S
local notation "tr" => sourceKPAdelicOutgoingRegularizedCompactTranslate K hζ S
local notation "W" => sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ S
local notation "seed" => sourceKPAdelicOutgoingRegularizedRetainedSeed K hζ S
local notation "value" => sourceKPAdelicOutgoingRegularizedRetainedValue K hζ S

local instance sourceKPAdelicOutgoingRetainedBorelAmbientAddCommGroup (s : ℂ) : AddCommGroup (V s) :=
  Submodule.addCommGroup _

def sourceKPAdelicOutgoingRetainedBorelAction (s : ℂ) :
    Representation ℂ Bₛ (Rest → V (-s)) where
  toFun b :=
    { toFun := fun v r => ρ (-s) (Lᴮ b) (v r)
      map_add' := fun v w => funext (fun r => map_add (ρ (-s) (Lᴮ b)) (v r) (w r))
      map_smul' := fun a v => funext (fun r => map_smul (ρ (-s) (Lᴮ b)) a (v r)) }
  map_one' := by
    apply LinearMap.ext
    intro v
    funext r
    change ρ (-s) (Lᴮ 1) (v r) = v r
    rw [map_one Lᴮ,map_one (ρ (-s)),Module.End.one_apply]
  map_mul' b c := by
    apply LinearMap.ext
    intro v
    funext r
    change ρ (-s) (Lᴮ (b*c)) (v r) = ρ (-s) (Lᴮ b) (ρ (-s) (Lᴮ c) (v r))
    rw [map_mul Lᴮ,map_mul (ρ (-s)),Module.End.mul_apply]

local notation "act" => sourceKPAdelicOutgoingRetainedBorelAction K hζ S

theorem sourceKPAdelicOutgoingRegularizedRetainedCarrier_borel_mem (s : ℂ) (hs : 0 < s.re)
    (b : Bₛ) (v : Rest → V (-s)) (hv : v ∈ W s hs) : act s b v ∈ W s hs := by
  change v ∈ Submodule.span ℂ (Set.range (seed s hs)) at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨q,rfl⟩ := hv
    obtain ⟨c,a,ha⟩ := sourceKPLocalCompactProductBorelAction_cubeClasses K hζ S (-s) (b*D q.1)
    have he : act s b (seed s hs q) = (a : ℂ) • seed s hs (c,q.2) := by
      funext r
      let x := (tr s hs q.2).val r.val
      change ρ (-s) (Lᴮ b) (ρ (-s) (Lᴮ (D q.1)) x) =
        (a : ℂ) • ρ (-s) (Lᴮ (D c)) x
      have h := ha x
      rw [map_mul Lᴮ,map_mul (ρ (-s)),Module.End.mul_apply] at h
      exact h
    rw [he]
    exact (W s hs).smul_mem (a : ℂ) (Submodule.subset_span ⟨(c,q.2),rfl⟩)
  | zero => simpa only [map_zero] using (W s hs).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (W s hs).add_mem hx hy
  | smul a x _ hx => simpa only [map_smul] using (W s hs).smul_mem a hx

local instance sourceKPAdelicOutgoingRetainedBorelCarrierAddCommGroup (s : ℂ) (hs : 0 < s.re) :
    AddCommGroup (W s hs) := Submodule.addCommGroup _

def sourceKPAdelicOutgoingRegularizedRetainedBorelRepresentation (s : ℂ) (hs : 0 < s.re) :
    Representation ℂ Bₛ (W s hs) where
  toFun b := (act s b).restrict (sourceKPAdelicOutgoingRegularizedRetainedCarrier_borel_mem K hζ S s hs b)
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change act s 1 x.val = x.val
    rw [map_one,Module.End.one_apply]
  map_mul' b c := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change act s (b*c) x.val = act s b (act s c x.val)
    rw [map_mul,Module.End.mul_apply]

local notation "ρ₀" => sourceKPAdelicOutgoingRegularizedRetainedBorelRepresentation K hζ S

def sourceKPAdelicOutgoingRegularizedRetainedVector (s : ℂ) (hs : 0 < s.re) (g : Gₛ) : W s hs :=
  ⟨value s hs g,sourceKPAdelicOutgoingRegularizedRetainedValue_mem K hζ S s hs g⟩

local notation "v₀" => sourceKPAdelicOutgoingRegularizedRetainedVector K hζ S

theorem sourceKPAdelicOutgoingRegularizedRetainedVector_borel (s : ℂ) (hs : 0 < s.re)
    (b : Bₛ) (g : Gₛ) :
    v₀ s hs ((fun P => (b P).val)*g) = ρ₀ s hs b (v₀ s hs g) := by
  apply Subtype.ext
  funext r
  change (R s hs).val (L ((fun P => (b P).val)*g)*r.val) =
    ρ (-s) (Lᴮ b) ((R s hs).val (L g*r.val))
  rw [map_mul L,mul_assoc,← sourceKPLocalCompactProductBorelLift_val K hζ S b]
  exact (R s hs).property (Lᴮ b) (L g*r.val)

end
end ArtinMatthews
