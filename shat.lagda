\documentclass{report}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb F}}}
\newunicodechar{𝕃}{\ensuremath{\mathnormal{\mathbb L}}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal{\mathbb Z}}}
\newunicodechar{ℚ}{\ensuremath{\mathnormal{\mathbb Q}}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{⊤}{\ensuremath{\mathnormal\top}}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{→}{\ensuremath{\mathnormal\rightarrow}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{∉}{\ensuremath{\mathnormal\notin}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_\AgdaFontStyle{i}}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_\AgdaFontStyle{l}}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_\AgdaFontStyle{s}}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_\AgdaFontStyle{v}}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_\AgdaFontStyle{o}}}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{ᵘ}{\ensuremath{\mathnormal{^\AgdaFontStyle{u}}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal\uplus}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{∧}{\ensuremath{\mathnormal\land}}
\newunicodechar{≤}{\ensuremath{\mathnormal\leq}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_m}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{∸}{\ensuremath{\mathnormal\divdot}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{𝓁}{\ensuremath{\mathnormal{\mathcal l}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
\newunicodechar{χ}{\ensuremath{\mathnormal\chi}}
\newunicodechar{⊃}{\ensuremath{\mathnormal\supset}}
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}
\newunicodechar{⊔}{\ensuremath{\mathnormal\sqcup}}
\newunicodechar{⊓}{\ensuremath{\mathnormal\sqcap}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\IC\AgdaInductiveConstructor
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\newcommand\Xr[2]{\textrm{#1(#2)}}

\title{le me'oi .Agda.\ velcki be la'o zoi.\ \Xr{shat}{1} .zoi.\ noi ke'a smimlu la'o zoi.\ \Xr{ed}{1} .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle

\chapter{le vrici}

\begin{code}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --overlapping-instances #-}
{-# OPTIONS --instance-search-depth=10 #-}

open import IO
  using (
    Main;
    run;
    IO
  )
open import Data.Fin
  as 𝔽
  using (
    Fin
  )
open import Data.Nat
  as ℕ
  using (
    ℕ
  )
open import Data.Sum
  using (
    from-inj₁;
    map₁;
    inj₂;
    inj₁;
    _⊎_
  )
open import Function
  using (
    typeOf;
    _on_;
    flip;
    _∋_;
    _$_;
    _∘_;
    id
  )
  renaming (
    _|>_ to _▹_
  )
open import IO.Finite
  using (
    readFile
  )
open import Data.Bool
  using (
    if_then_else_
  )
open import Data.Char
  using (
    Char
  )
open import Data.List
  as 𝕃
  using (
    List;
    drop;
    take;
    _∷_;
    []
  )
open import Data.Maybe
  using (
    decToMaybe;
    from-just;
    nothing;
    Maybe;
    maybe;
    just
  )
open import Data.String
  using (
    unlines;
    String;
    lines
  )
open import Data.Product
  using (
    uncurry;
    proj₂;
    proj₁;
    _×_;
    _,_;
    ∃;
    Σ
  )
open import Relation.Nullary
  using (
    Dec;
    yes;
    no
  )
open import System.Environment
  using (
    getArgs
  )
open import Truthbrary.Data.Fin
  using (
    mink
  )
open import Truthbrary.Record.Eq
  using (
    _≟_
  )
open import Truthbrary.Record.SR
  using (
    readMaybe;
    show
  )
open import Data.Unit.Polymorphic
  using (
    ⊤
  )
open import Truthbrary.Record.LLC
  using (
    liliList;
    length;
    _++_;
    _∉_;
    cev;
    vec
  )
open import Truthbrary.Category.Monad
  using (
    _>>=_
  )
  renaming (
    map to mapₘ
  )
open import Truthbrary.Data.List.Split
  using (
    splitOn
  )
open import Relation.Binary.PropositionalEquality
  using (
    _≡_
  )

import Agda.Builtin.IO
  as ABIO
import Agda.Builtin.Unit
  as ABU
import Data.Fin.Properties
  as DFP
import Data.List.Properties
  as DLP
import Data.Maybe.Instances
import Data.List.Relation.Unary.All
  as 𝕃
  using (
    All
  )
\end{code}

\chapter{le se ctaipe}

\section{la'oi .\AgdaRecord{Buffer}.}
ni'o zabna ciksi la'oi .\AgdaRecord{Buffer}.\ fo ma bau la .lojban.

\begin{code}
record Buffer : Set
  where
  field
    datnyveicme : Maybe String
    lerpinste : List String
    cablerpinsle : Fin $ length lerpinste
  F = typeOf cablerpinsle
\end{code}

\subsection{tu'a la'oi .\D{Fin}.}
ni'o tu'a la'oi .\D{Fin}.\ nibli ko'a goi le su'u ro da poi ke'a ctaipe la'oi .\AgdaRecord{Buffer}.\ zo'u li su'o co'e ja nilzilcmi lo mu'oi zoi.\ \AgdaField{Buffer.lerpinste}\ .zoi.\ be da  .i pilno le co'e co ke na'e me mu'oi zoi.\ \F{if\AgdaUnderscore{}then\AgdaUnderscore{}else\AgdaUnderscore} .zoi.\ ki'u le su'u ko'a milxe ko'e goi le ka ce'u fegli la .varik.\ldots kei je ku'i cu mleca fi ko'e je le ka tu'a ce'u frili kei fe lo jalge be lo nu la'o zoi.\ \AgdaField{Buffer.cablerpinsle} .zoi.\ ctaipe la'o zoi.\ \Sym(\B x \Sym : \AgdaRecord{Buffer}\Sym) \Sym → \OpF{if} \AgdaNumber 0 \OpF{ℕ.≤} \F{length} \Sym(\AgdaField{Buffer.lerpinste} \B x\Sym) \OpF{then} \AgdaField{Buffer.F} \B x \OpF{else} \D ⊤\ .zoi.

\section{la'oi .\D{Cmd}.}
ni'o ctaipe ko'a goi la'o zoi.\ \D{Cmd} \B x\ .zoi.\ fa lo co'e be lo midnoi be fo la'o zoi.\ \Xr{ed}{1} .zoi.\ ja zo'e be'o poi ctaipe lo su'u tu'a ke'a racli

\newcommand\cibysumti[2]{ga je da du la'o zoi.\ \IC{#1} \B v \B z \AgdaUnderscore{}\ .zoi.\ gi da mapti lo konkatena be lo sinxa be la'oi .\B v.\ be'o bei lo me'oi .comma.\ bei lo sinxa be la'oi .\B z.\ be'o bei #2}
.i ro da poi ke'a ctaipe ko'a zo'u\ldots
\begin{itemize}
	\item ga jonai ga je da du la'o zoi.\ \IC{Jmina} \B v\ .zoi.\ gi da mapti lo konkatena be lo sinxa be la'oi .\B v.\ be'o bei zo'oi .a.\ gi
	\item ga jonai ga je da du la'o zoi.\ \IC{Jmini} \B v\ .zoi.\ gi da mapti lo konkatena be lo sinxa be la'oi .\B v.\ bei zo'oi .i.\ gi
	\item ga jonai ga je da du la'o zoi.\ \IC{Rejgau} \B v\ .zoi.\ gi da mapti lo konkatena be zo'oi .w.\ bei lo canlu lerfu bei la'oi .\B v.\ gi
	\item ga jonai \cibysumti{Vimcu}{zo'oi .d.} gi
	\item ga jonai \cibysumti{Muvgau}{zo'oi .m.} gi
	\item ga jonai \cibysumti{Basti}{zo'oi .c.} gi
	\item ga jonai \cibysumti{Cusku}{zo'oi .p.} gi
	\item \cibysumti{Namcusku}{zo'oi .n.}
\end{itemize}

\begin{code}
data Cmd (x : Buffer) : Set where
  Jmina : Buffer.F x → Cmd x
  -- | ni'o la .varik. cu cnikansa lo se rigni
  -- be le klamburi
  Jmini : Buffer.F x → Cmd x
  Rejgau : String → Cmd x
  Vimcu : (a b : Buffer.F x) → a 𝔽.≤ b → Cmd x
  Namcusku : typeOf Vimcu
  Basti : typeOf Vimcu
  Cusku : typeOf Vimcu
  Muvgau : typeOf Vimcu
\end{code}

\section{la'oi .\D{Cmdᵢₒ}.}
ni'o ro da poi ke'a ctaipe la'o zoi.\ \D{Cmdᵢₒ} \B x\ .zoi.\ zo'u\ldots
\begin{itemize}
	\item ga jonai ga je da du la'o zoi.\ \IC{Rejgauᵢₒ} \B a \B b\ .zoi.\ gi tu'a da rinka lo nu rejgau benji la'oi .\B a.\ lo datnyvei poi ke'a selcme la'oi .\B b.\ gi
	\item ga jonai ga je da du la'o zoi.\ \IC{Tciduᵢₒ} \B a \B b\ .zoi.\ gi tu'a da rinka tu'a lo ctaipe be la'oi .\AgdaRecord{Buffer}.\ poi ro de poi ke'a xi pa ctaipe lo me'oi .\F{BufF}.\ be ke'a xi re zo'u ga jonai lo meirmoi be de bei fo ko'e goi lo mu'oi zoi.\ \AgdaField{Buffer.lerpinste}\ .zoi.\ be ke'a cu meirmoi de fo ko'a goi la'o zoi.\ \AgdaField{Buffer.lerpinste} \B x\ .zoi.\ gi ga jonai ga je de zmadu la'oi .\B b.\ je cu dubjavme'a ko'i goi lo nilzilcmi be ko'o goi lo'i ro lerpinsle be lo datnyvei poi ke'a xi re selcme la'oi .\B b.\ gi lo meirmoi be da bei fo ko'e cu meirmoi be lo vujnu be da bei ko'i fo ko'o gi ga je da zmadu la'oi .\B b.\ jenai cu dubjavme'a ko'i gi lo meirmoi be da bei fo ko'e cu meirmoi lo vujni be da bei la'oi .\B b.\ fo ko'a gi
	\item ga je da du la'o zoi.\ \IC{Skami} \B x\ .zoi.\ gi tu'a da rinka lo nu .uniks.\ co'e la'oi .\B x.
\end{itemize}

\begin{code}
data Cmdᵢₒ (x : Buffer) : Set where
  Rejgauᵢₒ : String → String → Cmdᵢₒ x
  Tcidu : String → Buffer.F x → Cmdᵢₒ x
  Skami : String → Cmdᵢₒ x
\end{code}

\chapter{le fancu}

\section{la'oi .\F{binxo𝔽?}.}
ni'o ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{binxo𝔽?}\ \B x\ .zoi.\ gi la'o zoi.\ \IC{just} \B x\ .zoi.\ du la'o zoi.\ \F{mapₘ} \F{𝔽.toℕ} \OpF \$ \F{binxo𝔽?}\ \B x\ .zoi.\

\begin{code}
binxo𝔽? : {n : ℕ} → ℕ → Maybe $ Fin n
binxo𝔽? = mapₘ 𝔽.fromℕ< ∘ decToMaybe ∘ (ℕ._<? _)
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{binxo𝔽?}.\ mapti}

\begin{code}
module Binxo𝔽Veritas where
  pav : {n : ℕ}
      → (x : ℕ)
      → x ℕ.< n
      → just x ≡ mapₘ 𝔽.toℕ (binxo𝔽? {n} x)
  pav = {!!}
\end{code}

\section{la'oi .\F{romoivimcu}.}
ni'o la .varik.\ na birti lo du'u zabna ciksi la'oi .\F{romoivimcu}.\ bau la .lojban.\ fo ma kau

\begin{code}
romoivimcu : String → String
romoivimcu = S $ 𝕃.reverse ∘ 𝕃.drop 1 ∘ 𝕃.reverse
  where
  S = λ f → cev ∘ vec ∘ f ∘ cev ∘ vec
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{romoivimcu}.\ mapti}

\begin{code}
module RomoivimcuVeritas where
  pav : (x : String)
      → (_≡_
          (Data.String.toList $ romoivimcu x)
          (𝕃.take
            (length x ℕ.∸ 1)
            (Data.String.toList x)))
  pav = {!!}
\end{code}

\section{la'oi .\F{orsygenturfa'i}.}
ni'o ro da poi ke'a ctaipe ko'a goi la'o zoi.\ \D{Fin} \B n\ .zoi.\ zo'u ro de poi ke'a ctaipe ko'a zo'u ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{orsygenturfa'i} \B s\ .zoi.\ gi ga je da dubjavme'a de gi ga je ko'a me'oi .\IC{just}.\ lo .orsi be li ci bei da bei de bei lo ctaipe be lo su'u da dubjavme'a de gi la'oi .\B s.\ konkatena lo sinxa be da lo me'oi .comma.\ lo sinxa be de

ni'o pilno ko'a goi le me'oi .module.\ co'e ki'u le su'u tu'a ko'a filri'a lo nu ciksi lo ctaipe be le su'u mapti  .i la .varik.\ na jinvi le du'u sarcu fa lo nu ciksi lo steci be la'oi .\F{orgenturfa'i}.\ jenai zo'e bau la .lojban.
\begin{code}
module Orsygenturfa'i where
  ps : {n : ℕ} → List Char → Maybe $ Fin n
  ps = (_>>= binxo𝔽?) ∘ readMaybe ∘ cev ∘ vec

  spit : String → List $ List Char
  spit = splitOn ⦃ record {_≟_ = Data.Char._≟_} ⦄ ',' ∘ cev ∘ vec

  pork : {n : ℕ}
       → List $ Maybe $ Fin n
       → Maybe $ Σ (Fin n × Fin n) $ uncurry 𝔽._≤_
  pork (just a ∷ just b ∷ []) with a 𝔽.≤? b
  ... | yes x = just $ _ , x
  ... | no _ = nothing
  pork _ = nothing

  orsygenturfa'i : {n : ℕ}
                 → String
                 → Maybe $ Σ (Fin n × Fin n) $ uncurry 𝔽._≤_
  orsygenturfa'i = pork ∘ 𝕃.map ps ∘ spit

open Orsygenturfa'i
  using (
    orsygenturfa'i
  )
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{orsygenturfa'i}.\ mapti}

\begin{code}
module Orsygenturfa'iVeritas where
  pav : {n : ℕ}
      → (a b : Fin n)
      → (djb : a 𝔽.≤ b)
      → let showF = show ∘ 𝔽.toℕ in
        (_≡_
          (just $ (a , b) , djb)
          (orsygenturfa'i $ showF a ++ "," ++ showF b))
  pav a b djb = sym $ begin
    orsygenturfa'i (showF a ++ "," ++ showF b) ≡⟨ _≡_.refl ⟩
    pork (𝕃.map ps $ spit a,b) ≡⟨ cong pork uimint ⟩
    pork (just a ∷ just b ∷ []) ≡⟨ uimladu a b djb ⟩
    just ((a , b) , djb) ∎
    where
    open Orsygenturfa'i
    showF : {n : ℕ} → Fin n → String
    showF = show ∘ 𝔽.toℕ

    a,b = showF a ++ "," ++ showF b

    uimladu : {n : ℕ}
            → (x z : Fin n)
            → (djb : x 𝔽.≤ z)
            → (_≡_
                (pork $ just x ∷ just z ∷ [])
                (just $ (x , z) , djb))
    uimladu x z djb = {!!}
    open import Relation.Binary.PropositionalEquality
    open ≡-Reasoning
    uimint = begin
      𝕃.map ps (spit a,b) ≡⟨ {!!} ⟩
      𝕃.map ps (showF' a ∷ showF' b ∷ []) ≡⟨ _≡_.refl ⟩
      𝕃.map justF' (a ∷ b ∷ []) ≡⟨ DLP.map-cong₂ jFF' ⟩
      𝕃.map justF (a ∷ b ∷ []) ≡⟨ _≡_.refl ⟩
      justF a ∷  justF b ∷ [] ≡⟨ juste a b ⟩
      just a ∷  just b ∷ [] ∎
      where
      showF' : {n : ℕ} → Fin n → List Char
      showF' = cev ∘ vec ∘ show ∘ 𝔽.toℕ
      justF : {n : ℕ} → Fin n → Maybe $ Fin n
      justF = (_>>= binxo𝔽?) ∘ readMaybe ∘ showF
      justF' : {n : ℕ} → Fin n → Maybe $ Fin n
      justF' = ps ∘ cev ∘ vec ∘ showF
      justF≡just : {n : ℕ} → (x : Fin n) → justF x ≡ just x
      justF≡just = {!!}
      justF'≡just : {n : ℕ} → (x : Fin n) → justF' x ≡ just x
      justF'≡just = {!!}
      jFF' : 𝕃.All (λ x → justF' x ≡ justF x) $ a ∷ b ∷ []
      jFF' = justF'≡justF a 𝕃.All.∷ justF'≡justF b 𝕃.All.∷ 𝕃.All.[]
        where
        justF'≡justF : {n : ℕ} → (x : Fin n) → justF' x ≡ justF x
        justF'≡justF x = step-≡ _ (sym $ justF≡just x) $ justF'≡just x
      juste : {n : ℕ}
            → (x z : Fin n)
            → justF x ∷ justF z ∷ [] ≡ just x ∷ just z ∷ []
      juste x z = begin
        justF x ∷ justF z ∷ []
          ≡⟨ justF≡just x ▹ cong (λ n → n ∷ justF z ∷ []) ⟩
        just x ∷ justF z ∷ []
          ≡⟨ justF≡just z ▹ cong (λ n → just x ∷ n ∷ []) ⟩
        just x ∷ just z ∷ [] ∎
\end{code}

\section{la'oi .\F{reed}.}
ni'o ga jonai la'oi .\IC{nothing}.\ du ko'a goi la'o zoi.\ \F{reed} \B x \B s\ .zoi.\ gi ga je la'oi .\B s.\ midnoi fo la'o zoi.\ \Xr{ed}{1} .zoi.\ je cu mapti la'o zoi.\ \D{Cmd} \B x\ .zoi.\ gi ko'a me'oi .\IC{just}.\ lo mapti be la'oi .\B s.

\begin{code}
reed : (x : Buffer) → String → Maybe $ Cmd x
reed x s = 𝕃.head $ 𝕃.mapMaybe id terp
  where
  r = romoivimcu s
  romoi = 𝕃.last ∘ Data.String.toList
  terp : List $ Maybe $ Cmd x
  terp = uux ∷ pav ∷ rel ∷ []
    where
    uux : Maybe $ Cmd x
    uux with 𝕃.map Data.String.fromList $ splitOn ' ' $ cev $ vec s
    ... | "w" ∷ x = just $ Rejgau $ 𝕃.foldr Data.String._<+>_ "" x
    ... | _ = nothing
    rel : Maybe $ Cmd x
    rel with orsygenturfa'i r , romoi s
    ... | (just ((a , b) , d) , just 'c') = just $ Basti a b d
    ... | (just ((a , b) , d) , just 'd') = just $ Vimcu a b d
    ... | (just ((a , b) , d) , just 'm') = just $ Muvgau a b d
    ... | (just ((a , b) , d) , just 'n') = just $ Namcusku a b d
    ... | (just ((a , b) , d) , just 'p') = just $ Cusku a b d
    ... | _ , _ = nothing
    pav : Maybe $ Cmd x
    pav = pav' t $ romoi s
      where
      pav' : Maybe $ Buffer.F x → Maybe Char → Maybe $ Cmd x
      pav' (just n) (just 'a') = just $ Jmina n
      pav' (just n) (just 'i') = just $ Jmini n
      pav' _ _ = nothing
      t = readMaybe i >>= binxo𝔽?
        where
        i = cev $ vec $ f $ cev $ vec s
          where
          f = λ l → 𝕃.take (length l ℕ.∸ 1) l
\end{code}

\subsection{le ctaipe be le su'u la'oi .\F{reed}.\ mapti}

\begin{code}
module ReedVeritas where
  private
    k₁ : (x : Buffer)
       → (a : Buffer.F x)
       → Char
       → String
    k₁ _ a x = show (𝔽.toℕ a) ++ Data.String.fromChar x

    k₃ : (x : Buffer)
       → (a b : Buffer.F x)
       → Char
       → String
    k₃ _ a b x = f a ++ "," ++ f b ++ Data.String.fromChar x
      where
      f = show ∘ 𝔽.toℕ

  ac : (x : Buffer)
     → (a : Buffer.F x)
     → just (Jmina a) ≡ reed x (k₁ x a 'a')
  ac = {!!}

  ic : (x : Buffer)
     → (a : Buffer.F x)
     → just (Jmini a) ≡ reed x (k₁ x a 'i')
  ic = {!!}

  mixer : (x : Buffer)
        → (a b : Buffer.F x)
        → (d : a 𝔽.≤ b)
        → just (Muvgau a b d) ≡ reed x (k₃ x a b 'm')
  mixer = {!!}

  vim : (x : Buffer)
      → (a b : Buffer.F x)
      → (d : a 𝔽.≤ b)
      → just (Vimcu a b d) ≡ reed x (k₃ x a b 'd')
  vim = {!!}

  uip : (x : Buffer)
      → (s : String)
      → (' ' ∉ s)
      → (_≡_
          (just $ Rejgau s)
          (reed x $ "w " ++ s))
  uip = {!!}
\end{code}

\section{la \F{kanji}}
ni'o la'o zoi.\ \F{kanji} \Sym\{\B x\Sym\} \B s\ .zoi.\ .orsi li re lo jalge be lo nu co'e la'oi .\B s.\ la'oi .\B x.\ kei zo'e poi ga jonai ke'a du la'oi .\IC{nothing}.\ gi ga jonai cadga fa lo nu cusku ke'a fo lo co'e co mu'oi glibau.\ standard output .glibau.\ gi\ldots ga je co'e gi la .varik.\ na birti lo du'u zabna ciksi tu'a ma kau bau la .lojban.

\begin{code}
kanji : {x : Buffer}
      → Cmd x
      → Σ Buffer $ Maybe ∘ _⊎_ String ∘ Cmdᵢₒ
kanji {x} (Cusku a b _) = x ,_ $ just $ inj₁ $ cmap i
  where
  BL = Buffer.lerpinste x
  cmap = Data.String.concat ∘ 𝕃.map (𝕃.lookup BL)
  i = 𝕃.filter (a 𝔽.≤?_) $ 𝕃.map Fintoℕ $ 𝕃.allFin $ 𝔽.toℕ b
    where
    Fintoℕ : {n : ℕ}
           → {x : Fin n}
           → Fin $ 𝔽.toℕ x
           → Fin n
    Fintoℕ f = 𝔽.inject≤ f $ DFP.toℕ≤n _
kanji {x} (Namcusku a b m) = x ,_ $ just $ inj₁ $ viiet kot
  where
  kot = from-inj₁ $ from-just $ proj₂ $ kanji {x} $ Cusku a b m
  viiet = unlines ∘ 𝕃.map stringCat' ∘ uin ∘ lines
    where
    stringCat' = λ (x , z) → show x ++ "\t" ++ z
    uin : List String → List $ ℕ × String
    uin = 𝕃.zip $ 𝕃.drop (𝔽.toℕ a) $ 𝕃.upTo $ 𝔽.toℕ b
kanji {x} (Vimcu a b _) = x' , nothing
  where
  x' = record x {
    cablerpinsle = {!!};
    lerpinste = 𝕃.map proj₂ $ 𝕃.filter nin $ indice Lz}
    where
    Lz = Buffer.lerpinste x
    indice = λ x → 𝕃.zip (𝕃.allFin $ length x) x
    nin : (x : _)
        → (Dec $ _∉_ ⦃ liliList ⦄ ⦃ record {_≟_ = 𝔽._≟_} ⦄
            (proj₁ x)
            (𝕃.map
              (flip 𝔽.inject≤ $ DFP.toℕ≤n _)
              (𝕃.drop (𝔽.toℕ a) $ 𝕃.allFin $ 𝔽.toℕ b)))
    nin _ = _ ≟ _
kanji {x} (Muvgau a b _) = x' , nothing
  where
  x' = record x {
    cablerpinsle = mink (Buffer.cablerpinsle x) {!!};
    lerpinste = {!!}
    }
kanji {x} (Jmina a) = x ,_ $ just $ inj₂ $ Tcidu "/dev/stdin" a
kanji = {!!}
\end{code}

\subsection{le ctaipe be le su'u la \F{kanji}\ cu mapti}

\begin{code}
module KanjyVeritas where
  dub₂ : (x : Buffer)
       → (a b : Buffer.F x)
       → (d : a 𝔽.≤ b)
       → let K = λ f → kanji {x} $ f a b d in
         let i = _≡_ x ∘ proj₁ ∘ K in
         i Cusku × i Namcusku
  dub₂ _ _ _ _ = _≡_.refl , _≡_.refl

  pindices : (x : Buffer)
           → (a b : Buffer.F x)
           → (d : a 𝔽.≤ b)
           → let K = proj₂ $ kanji {x} $ Cusku a b d in
             let L = lines $ from-inj₁ $ from-just K in
             (_≡_
               (𝕃.head L)
               (just $ 𝕃.lookup (Buffer.lerpinste x) a))
           × (_≡_
               (𝕃.last L)
               (just $ 𝕃.lookup (Buffer.lerpinste x) b))
  pindices = {!!}

  muvdusin : (x : Buffer)
           → (a b : Buffer.F x)
           → (d : a 𝔽.≤ b)
           → let x' = proj₁ $ kanji {x} $ Muvgau a b d in
             (kanji {x} (Muvgau a b d) ≡ (x' , nothing))
           × (Σ
               ((_≡_ on (length ∘ Buffer.lerpinste)) x x')
               (λ e →
                 (_≡_
                   (𝕃.lookup (Buffer.lerpinste x) a)
                   (𝕃.lookup (Buffer.lerpinste x') $ mink a e))))
           × let L = Buffer.lerpinste in
             (_≡_ on (𝕃.take (𝔽.toℕ a ℕ.⊓ 𝔽.toℕ b) ∘ L)) x x'
           × (_≡_ on (𝕃.drop (𝔽.toℕ a ℕ.⊔ 𝔽.toℕ b) ∘ L)) x x'
  muvdusin = {!!}

  jminac : (x : Buffer)
         → (a : Buffer.F x)
         → (_≡_
             (kanji {x} $ Jmina a)
             (x ,_ $ just $ inj₂ $ Tcidu "/dev/stdin" a))
  jminac _ _ = _≡_.refl
\end{code}

\section{la'oi .\F{main}.}
ni'o zabna ciksi la'oi .\F{main}.\ fo ma bau la .lojban.

\begin{code}
{-# NON_TERMINATING #-}
main : Main
main = run $ IO.lift snurytcati IO.>> getArgs IO.>>= uic ∘ 𝕃.head
  where
  postulate snurytcati : ABIO.IO ABU.⊤
  {-# FOREIGN GHC import System.OpenBSD.Plegg #-}
  {-# COMPILE GHC snurytcati = plegg [RPath, WPath, Stdio] #-}
  uic : Maybe String → IO ⊤
  uic c = maybe mkDef (IO.pure def) c IO.>>= lupe
    where
    def = record {
      datnyveicme = nothing;
      lerpinste = "" ∷ List.[];
      cablerpinsle = 𝔽.zero
      }
    mkDef : _
    mkDef c = uit ∘ Data.String.lines IO.<$> readFile c
      where
      uit : _ → _
      uit [] = record def {datnyveicme = just c}
      uit x@(_ ∷ _) = record {
        datnyveicme = just c;
        lerpinste = x;
        cablerpinsle = 𝔽.opposite 𝔽.zero
        }
    lupe : (x : Buffer) → IO ⊤
    lupe x = IO.getLine IO.>>= f ∘ reed x
      where
      f : Maybe $ Cmd x → IO ⊤
      f nothing = IO.putStrLn "?" IO.>> lupe x
      f (just c) with kanji c
      ... | x' , nothing = lupe x'
      ... | x' , just (inj₁ z) = IO.putStrLn z IO.>> lupe x'
      ... | x' , just (inj₂ z) = {!!}
\end{code}
\end{document}
