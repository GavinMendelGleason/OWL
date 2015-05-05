
module OWL where 

open import Data.Empty
open import Function
open import Data.Unit hiding (setoid ; _≤_ )
open import Data.Product
open import Data.Sum
open import Level
open import Relation.Nullary
open import Relation.Unary hiding (Decidable)
open import Relation.Binary using (Setoid; IsEquivalence) 
open import Relation.Binary.Core hiding (_⇒_)
open import Data.Nat hiding (_⊔_) renaming (suc to nsuc ; zero to nzero)
open import Data.Vec hiding (_∈_)

data Facet : Set where 
  length : Facet
  minLength : Facet 
  fpattern : Facet
  minInclusive : Facet
  maxInclusive : Facet
  minExclusive : Facet
  maxExclusive : Facet
  totalDigits : Facet 
  fractionDigits : Facet


{-------------------------------------------------------------------------

  A vocabulary (or signature) V = ( NC , NPo , NPd , NI , ND , NV ) is a 6-tuple where
  
  NC is a set of OWL classes,
  NPo is a set of object properties,
  NPd is a set of data properties,
  NI is a set of individuals, and
  ND is a set of datatypes each associated with a positive integer datatype arity,
  NV is a set of well-formed constants. 

Note: There is no reason for separate ND / NV.  These can be rolled into a single syntax 
and given a joint interpretation function.
-}

module _ (URI : Set)
         (_≅_URI : Rel URI zero) -- Congruence relation over 
         (_≟_URI : Decidable _≅_URI) -- Decidability of equivalence over individuals
         (Literal : Set) -- Constants
         (Δᴵ : Set) -- Object Domain
         (Δᴰ : Set) -- Data Domain
         (_ᶜ : URI → Pred Δᴵ zero) -- Interpretation of classes
         (_ᴰᵀ : URI → Pred Δᴰ zero) -- Interpretation of datatypes
         (_ᴸᵀ : Literal → Δᴰ) -- Interpretation of constants
         (_ᴵ : URI → Δᴵ) -- Interpretation of individuals
         (_ᴰ : URI → Δᴰ) -- Interpretation of individual data points 
         (_ᴰᴾ : URI → Pred (Δᴵ × Δᴰ) zero) -- interpretation of data properties
         (_ᴼᴾ : URI → Pred (Δᴵ × Δᴵ ) zero) -- interpretation of object properties
         (_ᶠᴬ : Facet × Literal → Pred Δᴰ zero)
         (owlThing : URI)
         (owlNothing : URI)
         (owlThingLaw : owlThing ᶜ ≡ U)
         (owlNothingLaw : owlNothing ᶜ ≡ ∅)
         (owlTopObjectProperty : URI)
         (owlBottomObjectProperty : URI)
         (owlTopObjectPropertyLaw : owlTopObjectProperty ᴼᴾ ≡ U)
         (owlBottomObjectPropertyLaw : owlBottomObjectProperty ᴼᴾ ≡ ∅)
         (owlTopDataProperty : URI) 
         (owlBottomDataProperty : URI)
         (owlTopDataPropertyLaw : owlTopDataProperty ᴰᴾ ≡ U)
         (owlBottomDataPropertyLaw : owlBottomDataProperty ᴰᴾ ≡ ∅)
         (♯OP : Pred (Δᴵ × Δᴵ) zero → ℕ) -- cardinality of objects
         (♯DP : Pred (Δᴵ × Δᴰ) zero → ℕ) -- cardinality of datatypes
  where

  
  data DataType : Set where
    DT : URI → DataType

  data OwlClass : Set where 
    OC : URI → OwlClass
      
  data ObjectProperty : Set where 
    OP : URI → ObjectProperty
    IOP : URI → ObjectProperty 

  data DataProperty : Set where 
    DP : URI → DataProperty

  data Individual : Set where 
    Ind : URI → Individual

  {-
  inverseObjectProperty := 'InverseObjectProperty' '(' objectPropertyExpression ')'
  objectPropertyExpression := objectPropertyURI | inverseObjectProperty
  -}

      
  {- 
  dataComplementOf := 'DataComplementOf' '(' dataRange ')'
  dataOneOf := 'DataOneOf' '(' constant { constant } ')'
  datatypeFacet :=
                'length' | 'minLength' | 'maxLength' | 'pattern' |
                'minInclusive' | 'minExclusive' | 'maxInclusive' | 'maxExclusive' |
                'totalDigits' | 'fractionDigits'
  restrictionValue := constant
  datatypeRestriction := 'DatatypeRestriction' '(' dataRange datatypeFacet restrictionValue { datatypeFacet restrictionValue } ')'
  dataRange := datatypeURI | dataComplementOf | dataOneOf | datatypeRestriction
  -}

  data DataRange : Set where 
    DataTypeRange : DataType → DataRange
    DataComplimentOf : DataRange → DataRange
    DataOneOf : ∀ {n} → Vec Literal n → DataRange
    DataTypeRestriction : DataRange → Facet → Literal → DataRange
    
  {- 
  description := owlClassURI | objectUnionOf | objectIntersectionOf | objectComplementOf | objectOneOf |
  objectAllValuesFrom | objectSomeValuesFrom | objectExistsSelf | objectHasValue |
  objectMinCardinality | objectMaxCardinality | objectExactCardinality |
  dataAllValuesFrom | dataSomeValuesFrom | dataHasValue |
  dataMinCardinality | dataMaxCardinality | dataExactCardinality

  cardinality := nonNegativeInteger
  objectMinCardinality := 'ObjectMinCardinality' '(' cardinality objectPropertyExpression [ description ] ')'
  objectMaxCardinality := 'ObjectMaxCardinality' '(' cardinality objectPropertyExpression [ description ] ')'
  objectExactCardinality := 'ObjectExactCardinality' '(' cardinality objectPropertyExpression [ description ] ')'

  objectUnionOf := 'ObjectUnionOf' '(' description description { description } ')'
  objectIntersectionOf := 'ObjectIntersectionOf' '(' description description { description } ')'
  objectComplementOf := 'ObjectComplementOf' '(' description ')'
  objectOneOf := 'ObjectOneOf' '(' individualURI { individualURI }')'

  objectAllValuesFrom := 'ObjectAllValuesFrom' '(' objectPropertyExpression description ')'
  objectSomeValuesFrom := 'ObjectSomeValuesFrom' '(' objectPropertyExpression description ')'
  objectExistsSelf := 'ObjectExistsSelf' '(' objectPropertyExpression ')'
  objectHasValue := 'ObjectHasValue' '(' objectPropertyExpression individualURI ')'

  dataAllValuesFrom := 'DataAllValuesFrom' '(' dataPropertyExpression { dataPropertyExpression } dataRange ')'
  dataSomeValuesFrom := 'DataSomeValuesFrom' '(' dataPropertyExpression { dataPropertyExpression } dataRange ')'
  dataHasValue := 'DataHasValue' '(' dataPropertyExpression constant ')'
  dataMinCardinality := 'DataMinCardinality' '(' cardinality dataPropertyExpression [ dataRange ] ')'
  dataMaxCardinality := 'DataMaxCardinality' '(' cardinality dataPropertyExpression [ dataRange ] ')'
  dataExactCardinality := 'DataExactCardinality' '(' cardinality dataPropertyExpression [ dataRange ] ')'
  -}

  data Description : Set where 
    OwlClassURI : OwlClass → Description
    ObjectUnionOf : Description → Description → Description 
    ObjectIntersectionOf : Description → Description → Description 
    ObjectComplementOf : Description → Description
    ObjectOneOf : Individual → Description
    ObjectAllValuesFrom : ObjectProperty → Description → Description
    ObjectSomeValuesFrom : ObjectProperty →  Description → Description 
    ObjectExistsSelf : ObjectProperty → Description
    ObjectHasValue : ObjectProperty → Individual → Description
    ObjectMinCardinality : ℕ → ObjectProperty → Description
    ObjectMaxCardinality : ℕ → ObjectProperty → Description
    ObjectExactCardinality : ℕ → ObjectProperty → Description
    ObjectMinClassCardinality : ℕ → ObjectProperty → Description → Description
    ObjectMaxClassCardinality : ℕ → ObjectProperty → Description → Description
    ObjectExactClassCardinality : ℕ → ObjectProperty → Description → Description
    DataAllValuesFrom : DataProperty → DataRange → Description
    DataSomeValuesFrom : DataProperty → DataRange → Description
    DataHasValue : DataProperty → Literal → Description
    DataMinCardinality : ℕ → DataProperty → Description
    DataMaxCardinality : ℕ → DataProperty → Description
    DataExactCardinality : ℕ → DataProperty → Description
    DataMinRangeCardinality : ℕ → DataProperty → DataRange → Description
    DataMaxRangeCardinality : ℕ → DataProperty → DataRange → Description
    DataExactRangeCardinality : ℕ → DataProperty → DataRange → Description


  {- 
  subClass := description
  superClass := description
  subClassOf := 'SubClassOf' '(' { annotation } subClass superClass ')'
  equivalentClasses := 'EquivalentClasses' '(' { annotation } description description { description } ')'
  disjointClasses := 'DisjointClasses' '(' { annotation } description description { description } ')'
  disjointUnion := 'DisjointUnion' '(' { annotation } owlClassURI description description { description } ')'
  classAxiom := subClassOf | equivalentClasses | disjointClasses | disjointUnion
  -}
  
  data ClassAxiom : Set where 
    SubClassOf : Description → Description → ClassAxiom
    EquivalentClasses : Description → Description → ClassAxiom
    DisjointClasses : Description → Description → ClassAxiom
    DisjointUnion : OwlClass → Description → Description → ClassAxiom

  {- 
  subObjectPropertyExpression := objectPropertyExpression | 'SubObjectPropertyChain' '(' objectPropertyExpression objectPropertyExpression { objectPropertyExpression } ')'
  subObjectPropertyOf := 'SubObjectPropertyOf' '(' { annotation } subObjectPropertyExpression objectPropertyExpression ')'
  equivalentObjectProperties := 'EquivalentObjectProperties' '(' { annotation } objectPropertyExpression objectPropertyExpression { objectPropertyExpression } ')'
  disjointObjectProperties := 'DisjointObjectProperties' '(' { annotation } objectPropertyExpression objectPropertyExpression { objectPropertyExpression } ')'
  objectPropertyDomain := 'ObjectPropertyDomain' '(' { annotation } objectPropertyExpression description ')'
  objectPropertyRange := 'ObjectPropertyRange' '(' { annotation } objectPropertyExpression description ')'
  inverseObjectProperties := 'InverseObjectProperties' '(' { annotation } objectPropertyExpression objectPropertyExpression ')'

  functionalObjectProperty := 'FunctionalObjectProperty' '(' { annotation } objectPropertyExpression ')'
  inverseFunctionalObjectProperty := 'InverseFunctionalObjectProperty' '(' { annotation } objectPropertyExpression ')'
  reflexiveObjectProperty := 'ReflexiveObjectProperty' '(' { annotation } objectPropertyExpression ')'
  irreflexiveObjectProperty := 'IrreflexiveObjectProperty' '(' { annotation } objectPropertyExpression ')'
  symetricObjectProperty := 'SymmetricObjectProperty' '(' { annotation } objectPropertyExpression ')'
  asymetricObjectProperty := 'AsymmetricObjectProperty' '(' { annotation } objectPropertyExpression ')'
  transitiveObjectProperty := 'TransitiveObjectProperty' '(' { annotation } objectPropertyExpression ')'

  objectPropertyAxiom :=
    subObjectPropertyOf | equivalentObjectProperties |
    disjointObjectProperties | inverseObjectProperties |
    objectPropertyDomain | objectPropertyRange |
    functionalObjectProperty | inverseFunctionalObjectProperty |
    reflexiveObjectProperty | irreflexiveObjectProperty |
    symetricObjectProperty | asymetricObjectProperty |
    transitiveObjectProperty
  -}

  data SubObjectProperty : Set where 
    SubObjectPropertyLift : ObjectProperty → SubObjectProperty
    SubObjectPropertyChain : ObjectProperty → ObjectProperty → SubObjectProperty

  data ObjectPropertyAxiom : Set where 
    SubObjectPropertyOf : SubObjectProperty → ObjectProperty → ObjectPropertyAxiom
    EquivalentObjectProperties : ObjectProperty → ObjectProperty → ObjectPropertyAxiom
    DisjointObjectProperties : ObjectProperty → ObjectProperty → ObjectPropertyAxiom
    InverseObjectProperties : ObjectProperty → ObjectPropertyAxiom
    ObjectPropertyDomain : ObjectProperty → ObjectPropertyAxiom 
    ObjectPropertyRange : ObjectProperty → ObjectPropertyAxiom
    FunctionalObjectProperties : ObjectProperty → ObjectProperty → ObjectPropertyAxiom
    InverseObjectProperty : ObjectProperty → ObjectPropertyAxiom
    ReflexiveObjectProperty : ObjectProperty → ObjectPropertyAxiom
    IrreflexiveObjectProperty : ObjectProperty → ObjectPropertyAxiom
    SymetricObjectProperty : ObjectProperty → ObjectPropertyAxiom
    AsymetricObjectProperty : ObjectProperty → ObjectPropertyAxiom
    TransitiveObjectProperty : ObjectProperty → ObjectPropertyAxiom

  {- 

  subDataPropertyOf := 'SubDataPropertyOf' '(' { annotation } dataPropertyExpression dataPropertyExpression ')'
  equivalentDataProperties := 'EquivalentDataProperties' '(' { annotation } dataPropertyExpression dataPropertyExpression { dataPropertyExpression } ')'
  disjointDataProperties := 'DisjointDataProperties' '(' { annotation } dataPropertyExpression dataPropertyExpression { dataPropertyExpression } ')'
  dataPropertyDomain := 'DataPropertyDomain' '(' { annotation } dataPropertyExpression description ')'
  dataPropertyRange := 'DataPropertyRange' '(' { annotation } dataPropertyExpression dataRange ')'
  functionalDataProperty := 'FunctionalDataProperty' '(' { annotation } dataPropertyExpression ')'

  dataPropertyAxiom :=
    subDataPropertyOf | equivalentDataProperties | disjointDataProperties |
    dataPropertyDomain | dataPropertyRange | functionalDataProperty
  -}

  data DataPropertyAxiom : Set where 
    SubDataPropertyOf : DataProperty → DataProperty → DataPropertyAxiom
    EquivalentDataProperties : DataProperty → DataProperty → DataPropertyAxiom
    DisjointDataProperties : DataProperty → DataProperty → DataPropertyAxiom
    DataPropertyDomain : DataProperty → DataPropertyAxiom
    DataPropertyRange : DataProperty → DataPropertyAxiom
    FunctionalDataProperty : DataProperty → DataPropertyAxiom
    

  {- 
  sameIndividual := 'SameIndividual' '(' { annotation } individualURI individualURI { individualURI } ')'
  differentIndividuals := 'DifferentIndividuals' '(' { annotation } individualURI individualURI { individualURI } ')'
  classAssertion := 'ClassAssertion' '(' { annotation } individualURI description ')'
    
  sourceIndividualURI := individualURI
  targetIndividualURI := individualURI
  objectPropertyAssertion := 'ObjectPropertyAssertion' '(' { annotation } objectPropertyExpression sourceIndividualURI targetIndividualURI ')'
  negativeObjectPropertyAssertion := 'NegativeObjectPropertyAssertion' '(' { annotation } objectPropertyExpression sourceIndividualURI targetIndividualURI ')'

  targetValue := constant
  dataPropertyAssertion := 'DataPropertyAssertion' '(' { annotation } dataPropertyExpression sourceIndividualURI targetValue ')'
  negativeDataPropertyAssertion := 'NegativeDataPropertyAssertion' '(' { annotation } dataPropertyExpression sourceIndividualURI targetValue ')'

  fact := sameIndividual | differentIndividuals | classAssertion |
    objectPropertyAssertion | negativeObjectPropertyAssertion |
    dataPropertyAssertion | negativeDataPropertyAssertion
  -}
  
  data Fact : Set where 
    SameIndividual : Individual → Individual → Fact
    DifferentIndividuals : Individual → Individual → Fact
    ClassAssertion : OwlClass → Individual → Fact
    ObjectPropertyAssertion : ObjectProperty → Individual → Individual → Fact
    NegativeObjectPropertyAssertion : ObjectProperty → Individual → Individual → Fact
    DataPropertyAssertion : DataProperty → Individual → Individual → Fact
    NegativeDataPropertyAssertion : DataProperty → Individual → Individual → Fact
  

  data Rule : Set where 
    FactRule : Fact → Rule
    ClassRule : ClassAxiom → Rule
    ObjectPropertyRule : ObjectPropertyAxiom → Rule
    DataProperytRule : DataPropertyAxiom → Rule
    DescriptionRule : Description → Rule
  
  Theory : ℕ → Set
  Theory n = Vec Rule n

  raise : ∀ {ℓ} {A : Set zero} → Pred A zero → Pred A ℓ
  raise  {ℓ} {_} p x = Lift {zero} {ℓ} (p x)


  domain : ∀ {A B : Set} → Pred (A × B) zero  → Pred A zero 
  domain {A} {B} p = λ x → Σ[ y ∈ B ] p (x , y)

  range : ∀ {A B : Set} → Pred (A × B) zero  → Pred B zero 
  range {A} {B} p = λ y → Σ[ x ∈ A ] p (x , y)

  ∣_∣r : DataRange → Pred Δᴰ zero
  ∣ DataTypeRange (DT t) ∣r = t ᴰᵀ
  ∣ DataComplimentOf r ∣r = ∁ ∣ r ∣r 
  ∣ DataOneOf v ∣r = foldr (λ _ → Pred Δᴰ zero) (λ c p → (λ x → x ≡ c ᴸᵀ) ∪ p) U v 
  ∣ DataTypeRestriction r x x₁ ∣r = ∣ r ∣r ∩ (x , x₁) ᶠᴬ

  ∣_∣c : Description → Pred Δᴵ zero
  ∣ OwlClassURI (OC x) ∣c = x ᶜ
  ∣ ObjectUnionOf xc xc₁ ∣c = ∣ xc ∣c ∪ ∣ xc₁ ∣c 
  ∣ ObjectIntersectionOf x x₁ ∣c = ∣ x ∣c ∩ ∣ x ∣c
  ∣ ObjectComplementOf x ∣c = ∁ (∣ x ∣c)
  ∣ ObjectOneOf (Ind x) ∣c = (λ x₁ → x ᴵ ≡ x₁)
  ∣ ObjectAllValuesFrom (OP p) c ∣c = λ x → ∀ (y : Δᴵ) → (x , y) ∈ p ᴼᴾ → y ∈ ∣ c ∣c
  ∣ ObjectAllValuesFrom (IOP p) c ∣c = λ x → ∀ (y : Δᴵ) → (y , x) ∈ p ᴼᴾ → y ∈ ∣ c ∣c
  ∣ ObjectSomeValuesFrom (OP p) c ∣c = λ x → Σ[ y ∈ Δᴵ ] (x , y) ∈ p ᴼᴾ × y ∈ ∣ c ∣c
  ∣ ObjectSomeValuesFrom (IOP p) c ∣c = λ x → Σ[ y ∈ Δᴵ ] (y , x) ∈ p ᴼᴾ × y ∈ ∣ c ∣c
  ∣ ObjectExistsSelf (OP p) ∣c = λ x → (x , x) ∈ p ᴼᴾ
  ∣ ObjectExistsSelf (IOP p) ∣c = λ x → (x , x) ∈ p ᴼᴾ
  ∣ ObjectHasValue (OP p) (Ind v) ∣c = λ x → (x , v ᴰ) ∈ p ᴰᴾ
  ∣ ObjectHasValue (IOP p) (Ind v) ∣c = ∅
  ∣ ObjectMinCardinality n (OP p) ∣c = λ x → ♯OP( λ prop → (prop ∈ p ᴼᴾ) × x ∈ domain (p ᴼᴾ) ) ≥ n
  ∣ ObjectMinCardinality n (IOP p) ∣c = λ x → ♯OP (λ prop → prop ∈ p ᴼᴾ × x ∈ range (p ᴼᴾ)) ≥ n
  ∣ ObjectMaxCardinality n (OP p) ∣c = λ x → ♯OP (λ prop → prop ∈ p ᴼᴾ × x ∈ domain (p ᴼᴾ)) ≤ n
  ∣ ObjectMaxCardinality n (IOP p) ∣c = λ x → ♯OP (λ prop → prop ∈ p ᴼᴾ × x ∈ range (p ᴼᴾ)) ≤ n
  ∣ ObjectExactCardinality n (OP p) ∣c = λ x → ♯OP (λ prop → prop ∈ p ᴼᴾ × x ∈ domain (p ᴼᴾ)) ≡ n
  ∣ ObjectExactCardinality n (IOP p) ∣c = λ x → ♯OP (λ prop → prop ∈ p ᴼᴾ × x ∈ range (p ᴼᴾ)) ≡ n
  ∣ ObjectMinClassCardinality n (OP p) c ∣c = λ x → ♯OP( λ prop → (prop ∈ p ᴼᴾ) × x ∈ domain (p ᴼᴾ) × proj₂ prop ∈ ∣ c ∣c ) ≥ n
  ∣ ObjectMinClassCardinality n (IOP p) c ∣c = λ x → ♯OP (λ prop → prop ∈ p ᴼᴾ × x ∈ range (p ᴼᴾ) × proj₁ prop ∈ ∣ c ∣c ) ≥ n
  ∣ ObjectMaxClassCardinality n (OP p) c ∣c = λ x → ♯OP (λ prop → prop ∈ p ᴼᴾ × x ∈ domain (p ᴼᴾ) × proj₂ prop ∈ ∣ c ∣c ) ≤ n
  ∣ ObjectMaxClassCardinality n (IOP p) c ∣c = λ x → ♯OP (λ prop → prop ∈ p ᴼᴾ × x ∈ range (p ᴼᴾ) × proj₁ prop ∈ ∣ c ∣c ) ≤ n
  ∣ ObjectExactClassCardinality n (OP p) c ∣c = λ x → ♯OP (λ prop → prop ∈ p ᴼᴾ × x ∈ domain (p ᴼᴾ) × proj₂ prop ∈ ∣ c ∣c ) ≡ n
  ∣ ObjectExactClassCardinality n (IOP p) c ∣c = λ x → ♯OP (λ prop → prop ∈ p ᴼᴾ × x ∈ range (p ᴼᴾ) × proj₂ prop ∈ ∣ c ∣c ) ≡ n  
  ∣ DataAllValuesFrom (DP p) x₁ ∣c = λ x → ∀ y → y ∈ p ᴰᴾ → proj₂ y ∈ ∣ x₁ ∣r
  ∣ DataSomeValuesFrom (DP p) x₁ ∣c = λ x → Σ[ y ∈ (Δᴵ × Δᴰ) ] (y ∈ p ᴰᴾ → proj₂ y ∈ ∣ x₁ ∣r)
  ∣ DataHasValue (DP p) c ∣c = λ x → Σ[ y ∈ Δᴰ ] (y ≡ c ᴸᵀ × (x , y) ∈ p ᴰᴾ)
  ∣ DataMinCardinality n (DP p) ∣c  = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ)) ≥ n
  ∣ DataMaxCardinality n (DP p) ∣c = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ)) ≤ n
  ∣ DataExactCardinality n (DP p) ∣c = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ)) ≡ n
  ∣ DataMinRangeCardinality n (DP p) r ∣c = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ) × proj₂ prop ∈ ∣ r ∣r) ≥ n
  ∣ DataMaxRangeCardinality n (DP p) r ∣c = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ) × proj₂ prop ∈ ∣ r ∣r) ≤ n
  ∣ DataExactRangeCardinality n (DP p) r ∣c = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ) × proj₂ prop ∈ ∣ r ∣r) ≡ n


  ∣_∣ : Rule → Set 
  ∣ FactRule (SameIndividual (Ind x) (Ind x₁)) ∣ = x ᴵ ≡ x₁ ᴵ 
  ∣ FactRule (DifferentIndividuals (Ind x) (Ind x₁)) ∣ = x ᴵ ≡ x₁ ᴵ → ⊥
  ∣ FactRule (ClassAssertion (OC C) (Ind x)) ∣ =  x ᴵ ∈ C ᶜ
  ∣ FactRule (ObjectPropertyAssertion (OP x) (Ind x₁) (Ind x₂)) ∣ = (x₁ ᴵ , x₂ ᴵ) ∈ x ᴼᴾ
  ∣ FactRule (ObjectPropertyAssertion (IOP x) (Ind x₁) (Ind x₂)) ∣ = (x₂ ᴵ , x₁ ᴵ) ∈ x ᴼᴾ
  ∣ FactRule (NegativeObjectPropertyAssertion (OP x) (Ind x₁) (Ind x₂)) ∣ = (x₁ ᴵ , x₂ ᴵ) ∉ x ᴼᴾ
  ∣ FactRule (NegativeObjectPropertyAssertion (IOP x) (Ind x₁) (Ind x₂)) ∣ = (x₂ ᴵ , x₁ ᴵ) ∉ x ᴼᴾ
  ∣ FactRule (DataPropertyAssertion (DP x) (Ind x₁) (Ind x₂)) ∣ = (x₁ ᴵ , x₂ ᴰ) ∈ x ᴰᴾ
  ∣ FactRule (NegativeDataPropertyAssertion (DP x) (Ind x₁) (Ind x₂)) ∣ = (x₁ ᴵ , x₂ ᴰ) ∉ x ᴰᴾ
  ∣ ClassRule (SubClassOf x x₁) ∣ = {! Pred ∣ x !}
  ∣ ClassRule (EquivalentClasses x x₁) ∣ = {!!}
  ∣ ClassRule (DisjointClasses x x₁) ∣ = {!!}
  ∣ ClassRule (DisjointUnion x x₁ x₂) ∣ = {!!}
  ∣_∣ (ObjectPropertyRule x) = {!!}
  ∣_∣ (DataProperytRule x) = {!!}
  ∣_∣ (DescriptionRule x) = {!!}
 
