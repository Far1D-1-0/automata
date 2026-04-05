states = MapSet.new([:A, :B, :C, :D, :E, :F, :G, :H])
n = MapSet.size(states)
r = 3

get_map_reduction = fn
  st -> st |> Enum.reduce([MapSet.new()], fn x, acc -> [MapSet.union(hd(acc), x) | acc] end)
end

get_elem_reduction = fn
  st -> st |> Enum.reduce([MapSet.new()], fn x, acc -> [MapSet.put(hd(acc), x) | acc] end)
end

get_sections = fn
  st, r -> st |> get_elem_reduction.() |> Enum.filter(fn x -> MapSet.size(x) <= MapSet.size(st)-r end) |> Enum.map(fn x -> MapSet.difference(st, x) end) |> Enum.reverse()
end

get_pairs = fn
  sec ->
    {left, right} = sec |> Enum.split(1)
    right |> Enum.map(fn x -> [x | left] end) |> Enum.map(fn x -> MapSet.new(x) end)
end

join = fn
  map, insertion -> map |> Enum.map(fn x -> MapSet.put(insertion, x) end)
end

get_pools = fn
  st -> st |> get_elem_reduction.() |> Enum.reverse() |> Enum.map(fn x -> MapSet.difference(st, x) end)
end

get_combination_increment = fn
  pools, prefixes -> Enum.zip(pools, prefixes) |> Enum.flat_map(fn {pool, prefix} -> join.(pool, prefix) end)
end

sections = states |> get_sections.(r)

pairs = sections |> Enum.map(fn x -> get_pairs.(x) end)

pools = Enum.zip(pairs, sections) |> Enum.map(fn {pairs, section} -> MapSet.difference(section, hd(pairs)) |> get_pools.() end)

ci = Enum.zip(pools, pairs) |> Enum.map(fn {pools, prefixes} -> get_combination_increment.(pools, prefixes) end) # this would give the result of a combination of r = 3 of n elements



# get_pair_reduction = fn
#   pairs ->
#     pairs |> get_reduction.()
#   end

# combinations = sections |> Enum.map(fn x -> MapSet.to_list(x) |> Enum.split(r - 1) end) |> Enum.map(fn {left, right} -> {MapSet.new(left), MapSet.new(right)} end) |> Enum.map(fn {left, right} -> Enum.map(right, fn x -> MapSet.put(left, x) end) end)

# combinations = sections |> Enum.map(fn x -> MapSet.to_list(x) |> Enum.split(r - 1) end) |> Enum.map(fn {left, right} -> {MapSet.new(left), MapSet.new(right)} end) |> Enum.map(fn {left, right} -> Enum.map(right, fn x -> MapSet.put(left, x) end) end)
