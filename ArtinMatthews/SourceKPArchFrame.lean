module

public import ArtinMatthews.QuotientSectionHaar
public import ArtinMatthews.SourceKPArchGramQuotient


set_option backward.privateInPublic true
@[expose] public section

/-! The actual archimedean group frame from its Gram section and compact factor. -/
namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPArchFrameSection (q : SourceKPArchSymmetricSpace K hζ) :
    PGL(2, InfiniteAdeleRing K) :=
  ProjGenLinGroup.mk (sourceKPArchUpperHalfSection K hζ
    (sourceKPArchSymmetricHomeomorph K hζ q))

theorem sourceKPArchFrameSection_rightInverse (q : SourceKPArchSymmetricSpace K hζ) :
    QuotientGroup.mk (sourceKPArchFrameSection K hζ q) = q :=
  sourceKPArchSymmetricSection_coordinates K hζ q

theorem sourceKPArchFrameSection_continuous : Continuous (sourceKPArchFrameSection K hζ) :=
  QuotientGroup.continuous_mk.comp ((sourceKPArchUpperHalfSection_continuous K hζ).comp
    (sourceKPArchSymmetricHomeomorph K hζ).continuous)

def sourceKPArchFrameHomeomorph :
    PGL(2, InfiniteAdeleRing K) ≃ₜ
      (SourceKPArchUpperHalfSpace K × sourceKPArchBaseCompactSubgroup K hζ) :=
  (quotientSectionFrameHomeomorph (sourceKPArchBaseCompactSubgroup K hζ)
    (sourceKPArchFrameSection K hζ) (sourceKPArchFrameSection_rightInverse K hζ)
    (sourceKPArchFrameSection_continuous K hζ)).trans
      ((sourceKPArchSymmetricHomeomorph K hζ).prodCongr (Homeomorph.refl _))

theorem sourceKPArchFrameHomeomorph_fst (g : PGL(2, InfiniteAdeleRing K)) :
    (sourceKPArchFrameHomeomorph K hζ g).1 = sourceKPArchGramCoordinates K hζ g := rfl

end
end ArtinMatthews
