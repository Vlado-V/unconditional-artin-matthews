module

public import ArtinMatthews.SourceReflectionNumeratorReindex


set_option backward.privateInPublic true
@[expose] public section

/-! Row and column supports carried by the actual numerator reindex. -/

namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "Pr" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "f₀" => sourceReflectionActiveExponents K S₀

def SourceReflectionExteriorRowSupport (h n d : E) : Prop :=
  sourceReflectionIsSquarefree d ∧ Disjoint d.support (h.support ∪ n.support)

def SourceReflectionExteriorColumnSupport (f : Finset Pr) (c : E) : Prop :=
  sourceReflectionIsSquarefree c ∧ Disjoint c.support f

def sourceReflectionDigitIndex (h : E) (P : Pr) : Fin 6 :=
  ⟨h P % 6, Nat.mod_lt _ (by decide)⟩

theorem sourceReflectionExteriorSupport_of_index {h d : E} {f : Finset Pr}
    (hd : sourceReflectionIsSquarefree d) (hdh : Disjoint d.support h.support)
    (i : SourceReflectionSupportedTermIndex K S₀ f d) :
    SourceReflectionExteriorRowSupport K S₀ h i.val.2.1 d ∧
      SourceReflectionExteriorColumnSupport K S₀ f i.val.2.2.val ∧
      Disjoint d.support i.val.2.2.val.support ∧ Disjoint f i.val.2.1.support := by
  refine ⟨⟨hd, Finset.disjoint_union_right.mpr ⟨hdh, ?_⟩⟩,
    ⟨i.val.2.2.property, ?_⟩, ?_, ?_⟩
  · exact Finset.disjoint_left.mpr fun P hP hn =>
      (Finsupp.mem_support_iff.mp hn) (i.property.2 P hP).2.1
  · exact Finset.disjoint_left.mpr fun P hc hP =>
      (Finsupp.mem_support_iff.mp hc) (i.property.1 P hP).2.2
  · exact Finset.disjoint_left.mpr fun P hP hc =>
      (Finsupp.mem_support_iff.mp hc) (i.property.2 P hP).2.2
  · exact Finset.disjoint_left.mpr fun P hP hn =>
      (Finsupp.mem_support_iff.mp hn) (i.property.1 P hP).2.1

theorem sourceReflectionActiveChoice_subset {h : E} {f : Finset Pr}
    (hf : f ∈ sourceReflectionActiveChoices K S₀ h) : f ⊆ h.support :=
  Finset.mem_powerset.mp (Finset.mem_filter.mp hf).1

theorem sourceReflectionActiveChoice_digit_zero {h : E} {f : Finset Pr}
    (hf : f ∈ sourceReflectionActiveChoices K S₀ h) {P : Pr}
    (hP : P ∈ h.support) (hPf : P ∉ f) : sourceReflectionDigitIndex K S₀ h P = 0 := by
  apply Fin.ext
  exact not_not.mp (fun hn => hPf ((Finset.mem_filter.mp hf).2 P hP hn))

theorem sourceReflectionDigitIndex_row {h d : E} (hd : sourceReflectionIsSquarefree d)
    (hdh : Disjoint d.support h.support) {P : Pr} (hP : P ∈ d.support) :
    sourceReflectionDigitIndex K S₀ (h + d) P = 1 := by
  have hd1 : d P = 1 := reflectionSquarefreeExponent_support_one K S₀ ⟨d,hd⟩ ⟨P,hP⟩
  have hh0 := Finsupp.notMem_support_iff.mp (Finset.disjoint_left.mp hdh hP)
  apply Fin.ext
  simp [sourceReflectionDigitIndex, Finsupp.add_apply, hh0, hd1]

theorem sourceReflectionDigitIndex_off_row (h d : E) {P : Pr} (hP : P ∉ d.support) :
    sourceReflectionDigitIndex K S₀ (h + d) P = sourceReflectionDigitIndex K S₀ h P := by
  simp [sourceReflectionDigitIndex, Finsupp.add_apply, Finsupp.notMem_support_iff.mp hP]

theorem sourceReflectionActiveExponents_apply (f : Finset Pr) (P : Pr) :
    f₀ f P = if P ∈ f then 1 else 0 := Finsupp.onFinset_apply

theorem sourceReflectionExteriorRow_mem (h d : E) (P : Pr) :
    P ∈ (h + d).support ↔ P ∈ h.support ∪ d.support := by
  simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finset.mem_union]
  omega

end
end ArtinMatthews.SourceEulerAssembly
