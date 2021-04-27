#import "Basic";
#import "File";
#import "String";
#import "Random";

SAT :: enum s8 { UNASSIGNED :: TRUE|FALSE; FALSE :: 1; TRUE :: 2; CONFLICT :: 4; OKAY :: 0; }


Clause :: [..] int;

parse_sat_file :: (file_name: string)-> int, [..]Clause {
  text := read_entire_file(file_name);
  lines := split(text, "\n");
  clauses : [..]Clause;
  num_variables := -1;
  num_clauses   := -1;

  for line : lines {
    tokens := split(line, " ");
    if tokens.count == 0 {
      continue;
    }
    if equal(tokens[0], "c") {
      continue;
    }

    else if equal(tokens[0], "p") {
      num_variables = string_to_int(tokens[2]);
      num_clauses   = string_to_int(tokens[3]);
      array_reserve(*clauses, num_clauses);
    } else {
      clause : Clause;
      for token : tokens {
        val, correct := string_to_int(token);
        assert(correct, "Not parsed correctly, token=%, val=%", tokens, val);
        if val == 0
          break;
        array_add(*clause, val);
      }
      array_add(*clauses, clause);
    }
  }

  return num_variables, clauses;
}

naive_sat_solver :: (vars: [..]SAT, clauses: [..]Clause, level:=0)->bool {

  is_satisfiable :: (vars: [..]SAT, clauses: [..]Clause)->bool {
    for clause : clauses {
      cl := SAT.FALSE;
      for var : clause{
        bool_value : SAT = ---;
        if var < 0 {
          var = -var;
          bool_value = vars[var-1] ^ SAT.TRUE;
        } else {
          bool_value = vars[var-1];
        }

        cl = cl | bool_value;
      }
      if cl == SAT.FALSE {
        return false;
      }
    }
    return true;
  }


  if level >= vars.count then {
    return is_satisfiable(vars, clauses);
  }
  
  vars[level] = SAT.TRUE;
  if naive_sat_solver(vars, clauses, level + 1) {
    return true;
  }

  vars[level] = SAT.FALSE;
  if naive_sat_solver(vars, clauses, level + 1) {
    return true;
  }

  vars[level] = SAT.UNASSIGNED;
  return false;
}

GraphNode :: struct {
  clause := -1;
  level  := -1;
  edges  : [..] int;
}

ImplicationGraph :: [..] GraphNode;

boolean_constant_propagation :: (f: [..]Clause, a: [..]SAT, graph: ImplicationGraph, level := 0)-> SAT {
  while true {
    cont := false;
    for clause : f {
      clause_num := it_index;
      index, val := unit_propagation(a, clause);
      if val == SAT.CONFLICT {
        create_conflict_node(clause, graph, level, clause_num);
        return SAT.CONFLICT;
      }
      if index != -1 {
        a[index] = val;
        print("unit propagate: x%=% | level=% | clause num=% | clause:=%\n", index, a[index], level, clause_num, clause);
        create_node(clause, graph, index, level, clause_num);
        cont = true;
      }
    }

    if cont == false {
      break;
    }
  }

  return SAT.OKAY;

  unit_propagation :: (a: [..]SAT, clause : Clause)->int, SAT {
    count := 0;
    index := -1;
    value := SAT.UNASSIGNED;
    for var : clause {
      if var < 0 {
        var = -var - 1;
        if a[var] == SAT.FALSE then return -1, SAT.OKAY;
        if a[var] == SAT.UNASSIGNED {
          count = count + 1;
          index = var;
          value = SAT.FALSE;
        }
      } else {
        var = var - 1;
        if a[var] == SAT.TRUE then return -1, SAT.OKAY;
        if a[var] == SAT.UNASSIGNED {
          count = count + 1;
          index = var;
          value = SAT.TRUE;
        }
      }
      if count > 1 then return -1, SAT.UNASSIGNED;
    }
    if count == 1 {
      return index, value;
    } else {
      assert(count == 0);
      return -1, SAT.CONFLICT;
    }
  }

  create_node :: (clause: Clause, graph: ImplicationGraph, index: int, level: int, clause_num: int) {
    node := *graph[index];
    node.level  = level;
    node.clause = clause_num;
    for var : clause {
      if var < 0 {
        var = (-var)-1;
      } else {
        var = var - 1;
      } 
      if var != index {
        array_add(*node.edges, var);
      }
    }
  }

  create_conflict_node :: (clause: Clause, graph: ImplicationGraph, level: int, clause_num: int) {
    node := *graph[graph.count - 1];  // get last node i.e. the conflict node.
    node.level = level;
    node.clause = clause_num;
    for var : clause {
      if var < 0 {
        var = (-var)-1;
      } else {
        var = var - 1;
      } 
      array_add(*node.edges, var);
    }
  }
}

conflict_drive_clause_learning :: (num_vars: int, f: [..]Clause)->bool, [..]SAT {
  a : [..] SAT;
  graph : ImplicationGraph;
  init_vars(*a, *graph, num_vars);

  if boolean_constant_propagation(f, a, graph) == SAT.CONFLICT {
    return false, a;
  }

  level := 0;
  while true {
    found, index := has_unassigned_variables(a);
    if found == false then break;
    level = level + 1;
    decide(f, a);
    print("Deciding x%=%, level=%\n", index, a[index], level);
    while boolean_constant_propagation(f, a, graph, level) == SAT.CONFLICT {

      for node : graph {
        if node.level != -1
          print("x%@%, clause=%, edges=%\n",it_index, node.level, node.clause, node.edges);
      }

      b, c := analyze_conflict(f, a, graph, level);
      array_add(*f, c);
      print("adding c:=%\n", c);
      if b < 0 {
        return false, a;
      } else {
        backtrack(f, a, b, graph);
        level = b;
      }
    }
  }

  return true, a;

  // helper functions.
  init_vars :: (a: *[..]SAT, G: *ImplicationGraph, num_vars: int) {
    array_reserve(a, num_vars);
    array_reserve(G, num_vars+1);
    for i: 0..num_vars-1 {
      node: GraphNode;
      node.clause=-1;
      node.level=-1;
      array_add(a, SAT.UNASSIGNED);
      array_add(G, node);
    }
    node: GraphNode;
    node.clause=-1;
    node.level=-1;
    array_add(G, node);
  }

  backtrack :: (f: [..]Clause, a: [..]SAT, b: int, graph: ImplicationGraph) {
    for *node: graph {
      if node.level > b {
        val := it_index;
        if val < a.count {
          a[val] = SAT.UNASSIGNED;
        }
        node.clause = -1;
        node.level  = -1;
        array_reset(*node.edges);
      }
    }

    // reset conflict node.
    conflict := graph.count - 1;
    node := *graph[conflict];
    node.clause = -1;
    node.level  = -1;
    array_reset(*node.edges);
  }

  analyze_conflict :: (f: [..]Clause, a: [..]SAT, graph: ImplicationGraph, level: int)->(level: int, c: Clause) {
    d := level;
    if d == 0 return -1, None;

    conflict := graph.count-1; // conflict is always the last node.
    c: Clause;
    queue : [..]int;
    head := 0;
    array_add(*queue, conflict);

    antecedent(conflict, *c);
    while !one_lit_at_level(c, d) {
      t    := last_assigned_lit_at_level(c, d);
      v    := var_of_lit(t);
      ante := antecedent(t);
      print("Resolving ante=%, c=%,  t=%, v=%\n", ante, c, t, v);
      resolve(ante, *c, t, v);
      print("Resolved  ante=%, c=%,  t=%, v=%\n", ante, c, t, v);
    }
    b := asserting_level(c);
    return b, c;

    resolve :: (ante: Clause, clause: *Clause, t: int, v: SAT) {
      if ante.count == 0 return; // antecendent is empty, do nothing.
      t = t + 1;
      for var : <<clause {
        if var == t || -var == t {
          remove var;
        }
      }
      for a : ante {
        if a == t || -a == t continue;
        found, i := array_find(<<clause, a);
        if found continue;
        array_add(clause, a);
      }
    }

    antecedent :: (t: int, c: *Clause) #expand {
      node := *graph[t];  
      clause_num := node.clause;
      for var : f[clause_num] {
        array_add(c, var);
      }

      head = head + 1;
      for val: node.edges {
        if graph[val].level == node.level {
          array_add(*queue, val);
        }
      }
    }

    antecedent :: (t: int) -> Clause #expand {
      node := *graph[t];
      clause_num := node.clause;
      if clause_num == -1 return None;
      ret := f[clause_num];
      return ret;
    }

    last_assigned_lit_at_level :: (c: Clause, d: int)->int #expand {
      print("queue: %\n", queue);
      t := queue[head];
      head = head + 1;
      for val: graph[t].edges {
        if graph[val].level == d && !array_find(queue, val) {
          array_add(*queue, val);
        }
      }
      return t;
    }

    var_of_lit :: (t: int)->SAT #expand {
      return a[t];
    }

    one_lit_at_level :: (c: Clause, d: int)->bool #expand {
      count := 0;

      if c.count == 1 return true;

      for var: c {
        if var < 0 {
          var = -var - 1;
        } else {
          var = var - 1;
        }

        if graph[var].level == d {
          count = count + 1;
          if count > 1 {
            return false;
          }
        }
      }

      return true;
    }

    asserting_level :: (c: Clause)->int #expand {
      level := 0;
      for var: c {
        if var < 0 {
          var = -var - 1;
        } else {
          var = var - 1;
        }
        var_level := graph[var].level;
        if var_level == d continue;
        level = max(var_level, d);
      }
      return level;
    }
  }

  decide :: (f: [..]Clause, a: [..]SAT) #expand {
    // TODO: currently, we just pick a random value.
    rand := random_get();
    if rand & 1 {
      a[`index] = SAT.TRUE;
    } else {
      a[`index] = SAT.FALSE;
    }
    node := *graph[`index];
    node.level = level;
    node.clause = -1;
  }

  has_unassigned_variables :: (a: [..]SAT)->bool,int #expand {
    found, index := array_find(a, SAT.UNASSIGNED);
    return found, index;
  }

}

None : Clause; // ...Don't know if there's a better way to do this.

main :: () {
  args := get_command_line_arguments();
  if args.count == 1 {
    print("Please supply a *.cnf sat file to the program.\n");
    return;
  }

  // parse the sat file
  for i: 1..args.count - 1 {
    file_name := args[i];
    print("-----------------------\n");
    print("%\n", file_name);

    num_vars, clauses := parse_sat_file(file_name);
    // sat solver
    sat, vars := conflict_drive_clause_learning(num_vars, clauses);
 
    if sat {
      for var : vars {
        if var == SAT.TRUE {
          print(" x%,   ", it_index+1);
        } else if var == SAT.FALSE {
          print("-x%,   ", it_index+1);
        }
      }
      print("sat\n");
    } else {
      print("unsat\n");
    }
  }
}


