# Traducción de lambda-cáclculo a combinadores SKI (y viceversa).

Se defininen lambda-términos y términos SKI no tipados con índices de de Brujin.

También se definen esquemas de igualdad siguiendo [1] (cap. 9), adaptados para la presentación con índices de de Brujin.

Se implementan dos algoritmos: `bracket_abstraction` para traducción de lambda-términos a SKI, y `trlam` para el sentido contrario. Ambos están presentados en [1], aunque para el primero se utiliza una versión un poco simplificada descripta en [2].

Finalmente, se demuestra que ambas traducciones preservan igualdad.

## SKI

Se define un tipo inductivo `term` para términos, junto con dos refinamientos `lam` y `ski`. Se define la noción `nclosed` de término n-cerrado como término con a lo sumo $n$ variables libres (en realidad, $n$ representa una cota superior para los índices libres que aparecen en el término). También se definen convenientemente las nociones de variable libre y variable fresca.

## SKI.Equality

Se definen los esquemas de igualdad, siguiendo las reglas de reducción de ambos lenguajes. No se considera la $\eta$-igualdad para términos lambda.

Para combinadores SKI se contempla una forma restringida de extensionalidad a través de la regla $\zeta$, como presentada en [1]. Para esto, se define la noción auxiliar de termino _funcional_ `fnl`, para los cuales se aplicará esta regla.

_Nota de implementación_: en la regla `Zeta` se cuantifica universalmente sobre el alfabeto de variables (es decir, sobre `nat`), a diferencia de la presentación original, donde esta cuantificación es existencial. Esto se corresponde con la idea de que la extensionalidad debe valer para cualquier variable libre; es esperable que para $x$ no libre en $t$ ni $u$ valga:
$ t \; x = u \; x \iff
\forall \, y \, \notin FV(t, u). \;\; t \; y = u \; y$.


## BracketAbstraction

Se implementa la traducción de términos lambda a combinadores.
Para esto se define la función `abstract`, la cual abstrae un término SKI:

$tr_\lambda \;(abs \; t) = \lambda.\; tr_\lambda \; t$

Se demuestra que la traducción mapea términos cerrados a términos cerrados.


##  Subst

Se define la sustitución de términos. Esta se utiliza para la $\beta$-igualdad.

Se prueban resultados auxiliares en relación a variables libres
y al `shift`ing de términos.


## TrLam

Se define la traducción de combinadores a términos lambda.

## BracketAbstraction.Equality

Se demuestra que la bracket-abstraction preserva igualdad. Es decir:

$t = u \implies [|\,t\,|] = [|\,u\,|] $

Se siguen algunas de las ideas de la demostración planteada en [1].

Las mayores complicaciones surgen de demostrar este resultado para la $\beta$-igualdad, i.e. cuando $t$ $\beta$-reduce a $u$. Para esto se demuestran varios resultados auxiliares considerando la interacción entre $[| - |]$ y la sustitución.

Otro resultado interesante es que la abstracción para combinadores, como presentada en el algoritmo de braket-abstraction, preserva igualdad de términos SKI.
Esto se demuestra en `abstract_ski_eq`.

## Trlam.Equality

Se demuestra que la traducción de combinadores a lambda-cálculo preserva igualdad. Esto es:

$t = u \implies tr_\lambda\;t = tr_\lambda\; u$

Para esto se define la función auxiliar `abstractx`. Intuitivamente:

$ abstractx\; x\; t = \lambda x.\; t$

Concretamente, se verifica:

$ [v / x]\,t = (abstractx\; x\; t)\; v$

Luego se demuestra que, para esta noción de abstracción, se tiene una versión débil de la $\eta$-equivalencia, restringida a la imagen de términos SKI que sean _fnl_. Esto se hace en `abstractx_fnl`.

## Referencias

[1] J.R. Hindley, J.P. Seldin, 2008, _"Lambda-Calculus and Combinators - an Introduction"_

[2] O. Kiselyov, _"λ to SKI, Semantically"_