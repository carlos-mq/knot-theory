# knot-theory

An ongoing formalization of basic knot theory in Lean, following Murasugi's 'Knot Theory and Its Applications'.

At the moment, we follow the approach of representing knots and links as polygonal, with a finite set of vertices and edges.

The first goal of the project is proving Reidemeister's theorem.

## Current Structure

- `KnotTheory/PLLink.lean`: Piecewise linear (oriented) links are defined, along with the elementary knot moves and the lemmas necessary.

## To-do

1. Improve documentation.
2. Finish the proofs required for the inverse of elementary knot move (2) (see Murasugi, page 7).
3. Define the notion of a regular diagram of links (see Murasugi, page 26).
4. Define the notion of Reidemeister moves (see Murasugi, page 48).
