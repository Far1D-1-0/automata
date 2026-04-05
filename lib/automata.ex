defmodule Automata do

  def nfa_q do
    MapSet.new([:q0, :q1, :q2])
  end

  def nfa_alpha do
    MapSet.new([:a, :b])
  end

  def nfa_delta do
    %{
      :q0 => %{b: MapSet.new([:q1]), epsilon: MapSet.new([:q2])},
      :q1 => %{a: MapSet.new([:q1, :q2]), b: MapSet.new([:q2])},
      :q2 => %{a: MapSet.new([:q0])}
    }
  end

  def nfa_q0 do
    MapSet.new([:q0])
  end

  def nfa_accepted do
    MapSet.new([:q0])
  end

  def nfa do
    {Automata.nfa_q, Automata.nfa_alpha, Automata.nfa_delta, Automata.nfa_q0, Automata.nfa_accepted}
  end

  def nfa2_q do
    MapSet.new([0, 1, 2, 3])
  end

  def nfa2_alpha do
    MapSet.new([:a, :b])
  end

  def nfa2_delta do
    %{
      0 => %{a: MapSet.new([0, 1]), b: MapSet.new([0])},
      1 => %{b: MapSet.new([2])},
      2 => %{b: MapSet.new([3])},
      3 => %{}
    }
  end

  def nfa2_q0 do
    MapSet.new([0])
  end

  def nfa2_accepted do
    MapSet.new([3])
  end

  def nfa2 do
    {Automata.nfa2_q, Automata.nfa2_alpha, Automata.nfa2_delta, Automata.nfa2_q0, Automata.nfa2_accepted}
  end

  def section_split(list, n, r) do
    {left, right} = Enum.split(list, n)
    right |> sections(r) |> Enum.map(fn x -> [left | x] |> List.flatten() end)
  end

  def sections(list, 1) do
    {red, _acc} = Enum.map_reduce(list, list, fn _x, acc -> {acc, tl(acc)} end)
    red
  end
  def sections(list, r), do: sections(list, 1) |> Enum.filter(fn x -> length(x) >= r end)

  def my_join({inst, []}), do: inst
  def my_join({inst, list}) do
    list |> Enum.map(fn x -> [inst | [x]] |> List.flatten end)
  end

  def prefix(sec) do
    Enum.split(sec, 1) |> my_join()
  end

  def prefix_split(list, n) do
    {l, r} = Enum.split(list, n)
    [l | r]
  end

  def combinations(_set, 0), do: MapSet.new([MapSet.new([])])
  def combinations(set, 1), do: Enum.map(set, fn x -> MapSet.new([x]) end) |> MapSet.new()
  def combinations(set, 2), do: set |> sections(2) |> join_px_secs(2) |> lists_to_maps() # This case is not needed, already covered by sections_splits(secs, 0, _m) pattern
  def combinations(set, r), do: set |> sections(r) |> sections_splits(r - 2, 1) |> join_px_secs(r) |> lists_to_maps()

  def sections_splits(secs, n, m \\ 1)
  def sections_splits(secs, 0, _m), do: secs
  def sections_splits(secs, n, m) do
    Enum.flat_map(secs, fn x -> Automata.section_split(x, m, 2) end) |> sections_splits(n - 1, m + 1)
  end

  def join_px_secs(secs, r) do
    Enum.flat_map(secs, fn x -> prefix_split(x, r - 1) |> prefix end)
  end

  def lists_to_maps(list), do: Enum.map(list, fn x -> MapSet.new(x) end) |> MapSet.new()

  def power_set(set) do
    set
    |> MapSet.to_list
    |> power_set_helper(MapSet.size(set), MapSet.new())
  end

  def power_set_helper(_set, 0, acc), do: acc
  def power_set_helper(set, n, acc) do
    power_set_helper(set, n - 1, MapSet.union(combinations(set, n), acc))
  end

  def transition(delta, s, x), do: delta[s][x] |> transition_helper()

  def transition_helper(nil), do: MapSet.new()
  def transition_helper(t), do: t

  def prime_transition(delta, rr, x) do
    rr
    |> Enum.map(fn s -> transition(delta, s, x) end)
    |> Enum.reduce(fn d, acc -> MapSet.union(acc, d) end)
  end

  def epsilon(_delta, %{map: m, __struct__: _s}) when m == %{}, do: MapSet.new
  def epsilon(_delta, []), do: MapSet.new
  def epsilon(delta, states) do
    prime_transition(delta, states, :epsilon) |> MapSet.union(states)
  end

  def prime_accept(powerset, accepted_states) do
    powerset
    |> Enum.filter(fn rr -> !MapSet.disjoint?(rr, accepted_states) end) |> MapSet.new()
  end

  def build_dfa_delta(powerset, alphabet, nfa_delta) do # corregir
    powerset
    |> Enum.map(fn s -> {s, Enum.map(alphabet, fn x -> t = epsilon(nfa_delta, prime_transition(nfa_delta, s, x)); {x, t |> bdd_helper} end) |> Map.new} end) |> Map.new
  end

  def bdd_helper(%{map: m, __struct__: _s}) when m == %{}, do: MapSet.new
  def bdd_helper(t), do: MapSet.new([t])

  def determinize({q, al, d, q0, f}) do
    q_prime = q |> power_set
    al_prime = MapSet.put(al, :epsilon)
    d_prime = q_prime |> build_dfa_delta(al, d)
    q0_prime = MapSet.new([epsilon(d, q0)])
    f_prime = q_prime |> prime_accept(f)

    {q_prime, al_prime, d_prime, q0_prime, f_prime}
  end

  def drop_alphabet(delta) do
    delta |> Enum.map(fn {vx, m} -> {vx, Enum.reduce(m, MapSet.new, fn {_l, v}, acc -> MapSet.union(acc, v) end)} end) |> Map.new
  end

  def dfs(_graph, [], visited), do: visited
  def dfs(graph, [node | rest], visited) do
    if MapSet.member?(visited, node) do
      dfs(graph, rest, visited)
    else
      neighbors = Map.get(graph, node, MapSet.new) |> MapSet.to_list
      dfs(graph, neighbors ++ rest, MapSet.put(visited, node))
    end
  end

  def prune_helper(automata, _graph, 0), do: automata
  def prune_helper({q, al, d, q0, f}, graph, _n) do
    nodes = dfs(graph, MapSet.to_list(q0), MapSet.new)
    not_reached = MapSet.difference(q, nodes)

    prune_helper({nodes, al, Map.drop(d, MapSet.to_list(not_reached)), q0, MapSet.difference(f, not_reached)}, Map.drop(graph, MapSet.to_list(not_reached)), MapSet.size(not_reached))

  end

  def prune({q, al, d, q0, f}) do
    prune_helper({q, al, d, q0, f}, d |> drop_alphabet, -1)
  end


end

defmodule Automata.Write do

  def automata_to_graph({q, _al, d, q0, f}, name, path) do
    q_n = MapSet.difference(q, f)

    lines = start_graph(name) |> vertex_setup("init", [indent: 1, mark: :init])
    lines = Enum.reduce(q_n, lines, fn vx, acc -> vertex_setup(acc, vx |> any_to_string) end)
    lines = Enum.reduce(f, lines, fn vx, acc -> vertex_setup(acc, vx |> any_to_string, [indent: 1, mark: true]) end)

    lines = relation(lines, "init", q0, "start")
    lines = Enum.reduce(d, lines, fn {vx, ady}, acc -> Enum.reduce(ady, acc, fn {letter, sts}, acc2 -> relation(acc2, vx, sts, letter) end) end)

    lines = end_graph(lines)

    write_graph(lines, path)

  end

  def start_graph(name) do
    ["digraph #{name} {"]
  end

  def vertex_setup(list, vx, options \\ [indent: 1, mark: false])
  def vertex_setup(list, vx, options) do
    vx_n = any_to_string(vx)
    options = Map.new(options)
    list ++ ["#{indent(4 * options[:indent]) <> vx_n} [shape=#{which_shape(options[:mark])}];"]
  end

  def relation(list, vx1, vx2, rel, options \\ [indent: 1])
  def relation(list, vx1, vx2, rel, options) do
    vx1_n = any_to_string(vx1)
    vx2_l = MapSet.to_list(vx2)

    Enum.reduce(vx2_l, list, fn s, acc -> acc ++ ["#{indent(4 * options[:indent]) <> vx1_n} -> #{any_to_string(s)} [label=#{rel}];"] end)

    # list ++ ["#{indent(4 * options[:indent]) <> vx1_n} -> #{vx2_n} [label=#{rel}];"]
  end

  def end_graph(list) do
    list ++ ["}"]
  end

  def write_graph(list, path) do
    File.write(path, Enum.join(list, "\n"))
  end

  def which_shape(true), do: "doublecircle"
  def which_shape(false), do: "circle"
  def which_shape(:init), do: "point"

  def indent(n), do: String.duplicate(" ", n)

  def any_to_string(e) do
    cond do
      is_integer(e) -> Integer.to_string(e)
      is_atom(e) -> Atom.to_string(e)
      is_binary(e) -> e
      is_float(e) -> Float.to_string(e)
      is_list(e) -> Enum.map(e, fn x -> any_to_string(x) end) |> List.to_string()
      is_struct(e, MapSet) -> MapSet.to_list(e) |> any_to_string
    end
  end

end
