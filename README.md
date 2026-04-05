# Automata

Provides Autonoma.determinize/1 to convert a Non Deterministic Automaton to a Deterministic Automaton, both represented as a 5-touple containing {Q, Sigma, Delta, q0, F}.

Delta is the graph representation of the automaton as a Map with the following pattern:

%{
  k1 => %{x1: MapSet.new([states]), x2: MapSet,new([states]), ...},
  k2 => ...
  ...
}

It implements a custom powerset alogrithm to calulate Q'.

The module Automata.Write implements automata_to_graph/3 that generates the graphviz code for representing the given automaton graphically.
