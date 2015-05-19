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

open import Facet

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

module OWL (ClassURI : Set)
         (IndividualURI : Set)
         (DataTypeURI : Set)
         (DataPropertyURI : Set)
         (ObjectPropertyURI : Set)
         (Literal : Set) -- Constants
         (Δᴵ : Set) -- Object Domain
         (Δᴰ : Set) -- Data Domain
         (_ᶜ : ClassURI → Pred Δᴵ zero) -- Interpretation of classes
         (_ᴰᵀ : DataTypeURI → Pred Δᴰ zero) -- Interpretation of datatypes
         (_ᴸᵀ : Literal → Δᴰ) -- Interpretation of constants
         (_ᴵ : IndividualURI → Δᴵ) -- Interpretation of individuals
         (_ᴰᴾ : DataPropertyURI → Pred (Δᴵ × Δᴰ) zero) -- interpretation of data properties
         (_ᴼᴾ : ObjectPropertyURI → Pred (Δᴵ × Δᴵ ) zero) -- interpretation of object properties
         (_ᶠᴬ : Facet × Literal → Pred Δᴰ zero)
         (owlThing : ClassURI)
         (owlNothing : ClassURI)
         (owlThingLaw : owlThing ᶜ ≡ U)
         (owlNothingLaw : owlNothing ᶜ ≡ ∅)
         (owlTopObjectProperty : ObjectPropertyURI)
         (owlBottomObjectProperty : ObjectPropertyURI)
         (owlTopObjectPropertyLaw : owlTopObjectProperty ᴼᴾ ≡ U)
         (owlBottomObjectPropertyLaw : owlBottomObjectProperty ᴼᴾ ≡ ∅)
         (owlTopDataProperty : DataPropertyURI) 
         (owlBottomDataProperty : DataPropertyURI)
         (owlTopDataPropertyLaw : owlTopDataProperty ᴰᴾ ≡ U)
         (owlBottomDataPropertyLaw : owlBottomDataProperty ᴰᴾ ≡ ∅)
         (♯OP : Pred (Δᴵ × Δᴵ) zero → ℕ) -- cardinality of object properties
         (♯DP : Pred (Δᴵ × Δᴰ) zero → ℕ) -- cardinality of datatype properties
  where

  
  data DataType : Set where
    DT : DataTypeURI → DataType

  data OwlClass : Set where 
    OC : ClassURI → OwlClass
      
  data ObjectProperty : Set where 
    OP : ObjectPropertyURI → ObjectProperty
    IOP : ObjectPropertyURI → ObjectProperty 

  data DataProperty : Set where 
    DP : DataPropertyURI → DataProperty

  data Individual : Set where 
    Ind : IndividualURI → Individual

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
    InverseObjectProperties : ObjectProperty → ObjectProperty → ObjectPropertyAxiom
    ObjectPropertyDomain : ObjectProperty → Description → ObjectPropertyAxiom 
    ObjectPropertyRange : ObjectProperty → Description → ObjectPropertyAxiom
    FunctionalObjectProperty : ObjectProperty → ObjectPropertyAxiom
    InverseFunctionalObjectProperty : ObjectProperty → ObjectPropertyAxiom
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
    DataPropertyDomain : DataProperty → Description → DataPropertyAxiom
    DataPropertyRange : DataProperty  → DataRange → DataPropertyAxiom
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
    DataPropertyAssertion : DataProperty → Individual → Literal → Fact
    NegativeDataPropertyAssertion : DataProperty → Individual → Literal → Fact
  

  data Rule : Set where 
    FactRule : Fact → Rule
    ClassRule : ClassAxiom → Rule
    ObjectPropertyRule : ObjectPropertyAxiom → Rule
    DataProperytRule : DataPropertyAxiom → Rule
--    DescriptionRule : Description → Rule
  
  Theory : ℕ → Set
  Theory n = Vec Rule n

  domain : ∀ {A B : Set} → Pred (A × B) zero  → Pred A zero 
  domain {A} {B} p = λ x → Σ[ y ∈ B ] p (x , y)

  range : ∀ {A B : Set} → Pred (A × B) zero  → Pred B zero 
  range {A} {B} p = λ y → Σ[ x ∈ A ] p (x , y)

  ∣_∣dr : DataRange → Pred Δᴰ zero
  ∣ DataTypeRange (DT t) ∣dr = t ᴰᵀ
  ∣ DataComplimentOf r ∣dr = ∁ ∣ r ∣dr 
  ∣ DataOneOf v ∣dr = foldr (λ _ → Pred Δᴰ zero) (λ c p → (λ x → x ≡ c ᴸᵀ) ∪ p) U v 
  ∣ DataTypeRestriction r x x₁ ∣dr = ∣ r ∣dr ∩ (x , x₁) ᶠᴬ

  ∣_∣op : ObjectProperty → Pred (Δᴵ × Δᴵ) zero
  ∣_∣op (OP x) = x ᴼᴾ 
  ∣_∣op (IOP x) = ∁ (x ᴼᴾ)

  ∣_∣sop : SubObjectProperty → Pred (Δᴵ × Δᴵ) zero
  ∣_∣sop (SubObjectPropertyLift p) = ∣ p ∣op 
  ∣_∣sop (SubObjectPropertyChain p q) = ∣ p ∣op ⇒ ∣ q ∣op

  ∣_∣c : Description → Pred Δᴵ zero
  ∣ OwlClassURI (OC x) ∣c = x ᶜ
  ∣ ObjectUnionOf xc xc₁ ∣c = ∣ xc ∣c ∪ ∣ xc₁ ∣c 
  ∣ ObjectIntersectionOf x x₁ ∣c = ∣ x ∣c ∩ ∣ x₁ ∣c
  ∣ ObjectComplementOf x ∣c = ∁ (∣ x ∣c)
  ∣ ObjectOneOf (Ind x) ∣c = (λ x₁ → x ᴵ ≡ x₁)
  ∣ ObjectAllValuesFrom p c ∣c = λ x → ∀ (y : Δᴵ) → (x , y) ∈ ∣ p ∣op → y ∈ ∣ c ∣c
  ∣ ObjectSomeValuesFrom p c ∣c = λ x → Σ[ y ∈ Δᴵ ] (x , y) ∈ ∣ p ∣op × y ∈ ∣ c ∣c
  ∣ ObjectExistsSelf p ∣c = λ x → (x , x) ∈ ∣ p ∣op 
  ∣ ObjectHasValue (OP p) (Ind v) ∣c = λ x → (x , v ᴵ) ∈ p ᴼᴾ
  ∣ ObjectHasValue (IOP p) (Ind v) ∣c = ∁ (λ x → (x , v ᴵ) ∈ p ᴼᴾ)
  ∣ ObjectMinCardinality n p ∣c = λ x → ♯OP( λ prop → prop ∈ ∣ p ∣op × x ∈ domain ∣ p ∣op ) ≥ n
  ∣ ObjectMaxCardinality n p ∣c = λ x → ♯OP (λ prop → prop ∈ ∣ p ∣op × x ∈ domain ∣ p ∣op) ≤ n
  ∣ ObjectExactCardinality n p ∣c = λ x → ♯OP (λ prop → prop ∈ ∣ p ∣op × x ∈ domain ∣ p ∣op) ≡ n
  ∣ ObjectMinClassCardinality n p c ∣c = λ x → ♯OP( λ prop → (prop ∈ ∣ p ∣op) × x ∈ domain ∣ p ∣op × proj₂ prop ∈ ∣ c ∣c ) ≥ n
  ∣ ObjectMaxClassCardinality n p c ∣c = λ x → ♯OP (λ prop → prop ∈ ∣ p ∣op × x ∈ domain ∣ p ∣op  × proj₂ prop ∈ ∣ c ∣c ) ≤ n
  ∣ ObjectExactClassCardinality n p c ∣c = λ x → ♯OP (λ prop → prop ∈ ∣ p ∣op × x ∈ domain ∣ p ∣op × proj₂ prop ∈ ∣ c ∣c ) ≡ n
  ∣ DataAllValuesFrom (DP p) x₁ ∣c = λ x → ∀ y → y ∈ p ᴰᴾ → proj₂ y ∈ ∣ x₁ ∣dr
  ∣ DataSomeValuesFrom (DP p) x₁ ∣c = λ x → Σ[ y ∈ (Δᴵ × Δᴰ) ] (y ∈ p ᴰᴾ → proj₂ y ∈ ∣ x₁ ∣dr)
  ∣ DataHasValue (DP p) c ∣c = λ x → Σ[ y ∈ Δᴰ ] (y ≡ c ᴸᵀ × (x , y) ∈ p ᴰᴾ)
  ∣ DataMinCardinality n (DP p) ∣c  = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ)) ≥ n
  ∣ DataMaxCardinality n (DP p) ∣c = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ)) ≤ n
  ∣ DataExactCardinality n (DP p) ∣c = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ)) ≡ n
  ∣ DataMinRangeCardinality n (DP p) r ∣c = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ) × proj₂ prop ∈ ∣ r ∣dr) ≥ n
  ∣ DataMaxRangeCardinality n (DP p) r ∣c = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ) × proj₂ prop ∈ ∣ r ∣dr) ≤ n
  ∣ DataExactRangeCardinality n (DP p) r ∣c = λ x → ♯DP (λ prop → prop ∈ p ᴰᴾ × x ∈ domain (p ᴰᴾ) × proj₂ prop ∈ ∣ r ∣dr) ≡ n

  ∣_∣r : Rule → Set
  ∣ FactRule (SameIndividual (Ind x) (Ind x₁)) ∣r = x ᴵ ≡ x₁ ᴵ 
  ∣ FactRule (DifferentIndividuals (Ind x) (Ind x₁)) ∣r = x ᴵ ≡ x₁ ᴵ → ⊥
  ∣ FactRule (ClassAssertion (OC C) (Ind x)) ∣r =  x ᴵ ∈ C ᶜ
  ∣ FactRule (ObjectPropertyAssertion (OP x) (Ind x₁) (Ind x₂)) ∣r = (x₁ ᴵ , x₂ ᴵ) ∈ x ᴼᴾ
  ∣ FactRule (ObjectPropertyAssertion (IOP x) (Ind x₁) (Ind x₂)) ∣r = (x₂ ᴵ , x₁ ᴵ) ∈ x ᴼᴾ
  ∣ FactRule (NegativeObjectPropertyAssertion (OP x) (Ind x₁) (Ind x₂)) ∣r = (x₁ ᴵ , x₂ ᴵ) ∉ x ᴼᴾ
  ∣ FactRule (NegativeObjectPropertyAssertion (IOP x) (Ind x₁) (Ind x₂)) ∣r = (x₂ ᴵ , x₁ ᴵ) ∉ x ᴼᴾ
  ∣ FactRule (DataPropertyAssertion (DP p) (Ind x) l) ∣r = (x ᴵ , l ᴸᵀ) ∈ p ᴰᴾ
  ∣ FactRule (NegativeDataPropertyAssertion (DP p) (Ind x) l) ∣r = (x ᴵ , l ᴸᵀ) ∉ p ᴰᴾ
  ∣ ClassRule (SubClassOf sub super) ∣r = ∣ sub ∣c ⊆ ∣ super ∣c
  ∣ ClassRule (EquivalentClasses a b) ∣r = ∣ a ∣c ⊆ ∣ b ∣c × ∣ b ∣c ⊆ ∣ a ∣c
  ∣ ClassRule (DisjointClasses a b) ∣r = ∣ a ∣c ∩ ∣ b ∣c ⊆ ∅
  ∣ ClassRule (DisjointUnion (OC c) a b) ∣r = c ᶜ ⊆ ∣ a ∣c ∪ ∣ b ∣c × ∣ a ∣c ∩ ∣ b ∣c ⊆ ∅
  ∣ ObjectPropertyRule (SubObjectPropertyOf sub super) ∣r = ∣ sub ∣sop ⊆ ∣ super ∣op
  ∣ ObjectPropertyRule (EquivalentObjectProperties a b) ∣r = ∣ a ∣op ⊆ ∣ b ∣op × ∣ b ∣op ⊆ ∣ a ∣op
  ∣ ObjectPropertyRule (DisjointObjectProperties a b) ∣r = ∣ a ∣op ∩ ∣ b ∣op ⊆ ∅
  ∣ ObjectPropertyRule (InverseObjectProperties a b) ∣r = ∀ x y → (x , y) ∈ ∣ a ∣op × (y , x) ∈ ∣ b ∣op
  ∣ ObjectPropertyRule (ObjectPropertyDomain p c) ∣r = ∀ x y → (x , y) ∈ ∣ p ∣op → x ∈ ∣ c ∣c
  ∣ ObjectPropertyRule (ObjectPropertyRange p c) ∣r = ∀ x y → (x , y) ∈ ∣ p ∣op → y ∈ ∣ c ∣c
  ∣ ObjectPropertyRule (FunctionalObjectProperty p) ∣r = ∀ x y y' → (x , y) ∈ ∣ p ∣op × (x , y') ∈ ∣ p ∣op → y ≡ y'
  ∣ ObjectPropertyRule (InverseFunctionalObjectProperty p) ∣r = ∀ x x' y → (x , y) ∈ ∣ p ∣op × (x' , y) ∈ ∣ p ∣op → x ≡ x'
  ∣ ObjectPropertyRule (ReflexiveObjectProperty p) ∣r = ∀ x → (x , x) ∈ ∣ p ∣op
  ∣ ObjectPropertyRule (IrreflexiveObjectProperty p) ∣r = ∀ x → (x , x) ∉ ∣ p ∣op
  ∣ ObjectPropertyRule (SymetricObjectProperty p) ∣r = ∀ x y → (x , y) ∈ ∣ p ∣op × (y , x) ∈ ∣ p ∣op
  ∣ ObjectPropertyRule (AsymetricObjectProperty p) ∣r = ∀ x y → (x , y) ∈ ∣ p ∣op → (y , x) ∉ ∣ p ∣op
  ∣ ObjectPropertyRule (TransitiveObjectProperty p) ∣r = ∀ x y z → (x , y) ∈ ∣ p ∣op × (y , z) ∈ ∣ p ∣op → (x , z) ∈ ∣ p ∣op
  ∣ DataProperytRule (SubDataPropertyOf (DP a) (DP b)) ∣r = a ᴰᴾ ⊆ b ᴰᴾ
  ∣ DataProperytRule (EquivalentDataProperties (DP a) (DP b)) ∣r = a ᴰᴾ ⊆ b ᴰᴾ × b ᴰᴾ ⊆ a ᴰᴾ
  ∣ DataProperytRule (DisjointDataProperties (DP a) (DP b)) ∣r = a ᴰᴾ ∩ b ᴰᴾ ⊆ ∅
  ∣ DataProperytRule (DataPropertyDomain (DP p) c) ∣r = ∀ x y → (x , y) ∈ p ᴰᴾ → x ∈ ∣ c ∣c
  ∣ DataProperytRule (DataPropertyRange (DP p) dr) ∣r = ∀ x y → (x , y) ∈ p ᴰᴾ → y ∈ ∣ dr ∣dr
  ∣ DataProperytRule (FunctionalDataProperty (DP p)) ∣r = ∀ x y y' → (x , y) ∈ p ᴰᴾ × (x , y') ∈ p ᴰᴾ → y ≡ y'

  ∣_∣ : ∀ {n} → Theory n → Set
  ∣ [] ∣ = ⊤
  ∣ x ∷ t ∣ = ∣ x ∣r × ∣ t ∣
