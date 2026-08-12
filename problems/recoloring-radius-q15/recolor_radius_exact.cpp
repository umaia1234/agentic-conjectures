// Exact radius computations for graph-colouring reconfiguration graphs.
//
// This is an independent checker/searcher for Question 15 of
// Cambie--Cames van Batenburg--Cranston, EJC 33(1) (2026), P1.18.
// The vertices of C_k(G) are all labelled proper k-colourings of G; two are
// adjacent when exactly one vertex changes colour.  Eccentricity is invariant
// under a global permutation of colour names, so radius BFSs only need one
// restricted-growth representative from each colour-permutation orbit.

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <limits>
#include <numeric>
#include <queue>
#include <set>
#include <string>
#include <utility>
#include <vector>

using std::cerr;
using std::cout;
using std::pair;
using std::string;
using std::vector;

struct Graph {
  int n = 0;
  vector<pair<int, int>> edges;
  vector<uint32_t> neighbourhood;

  Graph(int order, vector<pair<int, int>> edge_list)
      : n(order), edges(std::move(edge_list)), neighbourhood(order, 0) {
    std::sort(edges.begin(), edges.end());
    for (auto [u, v] : edges) {
      neighbourhood[u] |= uint32_t(1) << v;
      neighbourhood[v] |= uint32_t(1) << u;
    }
  }

  bool has_edge(int u, int v) const {
    return (neighbourhood[u] >> v) & 1U;
  }
};

struct Result {
  bool connected = false;
  int radius = -1;
  uint32_t centre_code = 0;
  int states = 0;
  int orbit_representatives = 0;
};

static bool restricted_growth(const uint8_t* colour, int n) {
  // Canonical under arbitrary global renaming of colours.
  if (colour[0] != 0) return false;
  int largest_seen = 0;
  for (int v = 1; v < n; ++v) {
    if (colour[v] > largest_seen + 1) return false;
    largest_seen = std::max(largest_seen, int(colour[v]));
  }
  return true;
}

static Result exact_radius(const Graph& g, int k) {
  vector<uint32_t> power(g.n + 1, 1);
  for (int i = 1; i <= g.n; ++i) power[i] = power[i - 1] * k;
  const uint32_t universe = power[g.n];

  vector<int> id(universe, -1);
  vector<uint32_t> code;
  vector<uint8_t> digit;
  code.reserve(universe / 4);
  digit.reserve((universe / 4) * g.n);

  std::array<uint8_t, 20> colours{};
  for (uint32_t x = 0; x < universe; ++x) {
    uint32_t q = x;
    for (int v = 0; v < g.n; ++v) {
      colours[v] = q % k;
      q /= k;
    }
    bool proper = true;
    for (auto [u, v] : g.edges) {
      if (colours[u] == colours[v]) {
        proper = false;
        break;
      }
    }
    if (!proper) continue;
    id[x] = int(code.size());
    code.push_back(x);
    digit.insert(digit.end(), colours.begin(), colours.begin() + g.n);
  }

  Result answer;
  answer.states = int(code.size());
  if (code.empty()) return answer;

  // Materialise C_k(G).  This makes hundreds of exact BFSs inexpensive.
  vector<vector<int>> adjacency(code.size());
  for (int s = 0; s < int(code.size()); ++s) {
    const uint8_t* c = &digit[size_t(s) * g.n];
    for (int v = 0; v < g.n; ++v) {
      uint32_t forbidden = 0;
      uint32_t neighbours = g.neighbourhood[v];
      while (neighbours) {
        int u = __builtin_ctz(neighbours);
        neighbours &= neighbours - 1;
        forbidden |= uint32_t(1) << c[u];
      }
      for (int replacement = 0; replacement < k; ++replacement) {
        if (replacement == c[v] || ((forbidden >> replacement) & 1U)) continue;
        int64_t next_code = int64_t(code[s]) +
                            int64_t(replacement - c[v]) * power[v];
        int next = id[size_t(next_code)];
        if (next < 0) {
          cerr << "internal error: locally proper state absent\n";
          std::exit(2);
        }
        adjacency[s].push_back(next);
      }
    }
  }

  vector<int> distance(code.size(), -1);
  vector<int> touched;
  touched.reserve(code.size());
  vector<int> queue(code.size());

  auto bfs = [&](int source, int cutoff) -> pair<int, int> {
    int head = 0, tail = 0, eccentricity = 0;
    queue[tail++] = source;
    distance[source] = 0;
    touched.push_back(source);
    bool stopped = false;
    while (head < tail) {
      int here = queue[head++];
      int depth = distance[here];
      eccentricity = std::max(eccentricity, depth);
      // Once this source cannot improve the incumbent radius, its exact
      // eccentricity is irrelevant.  Connectivity is checked separately.
      if (cutoff >= 0 && eccentricity >= cutoff) {
        stopped = true;
        break;
      }
      for (int next : adjacency[here]) {
        if (distance[next] >= 0) continue;
        distance[next] = depth + 1;
        touched.push_back(next);
        queue[tail++] = next;
      }
    }
    int reached = int(touched.size());
    for (int vertex : touched) distance[vertex] = -1;
    touched.clear();
    return {eccentricity, stopped ? -reached : reached};
  };

  auto [ignored_eccentricity, reached] = bfs(0, -1);
  (void)ignored_eccentricity;
  if (reached != int(code.size())) return answer;
  answer.connected = true;

  vector<int> sources;
  for (int s = 0; s < int(code.size()); ++s) {
    if (restricted_growth(&digit[size_t(s) * g.n], g.n)) sources.push_back(s);
  }
  answer.orbit_representatives = int(sources.size());

  // A double-sweep midpoint is often central and gives a strong initial bound.
  auto full_distances = [&](int source) {
    vector<int> d(code.size(), -1);
    std::queue<int> q;
    d[source] = 0;
    q.push(source);
    while (!q.empty()) {
      int here = q.front();
      q.pop();
      for (int next : adjacency[here]) {
        if (d[next] >= 0) continue;
        d[next] = d[here] + 1;
        q.push(next);
      }
    }
    return d;
  };
  vector<int> d0 = full_distances(0);
  int far = int(std::max_element(d0.begin(), d0.end()) - d0.begin());
  vector<int> df = full_distances(far);
  int other = int(std::max_element(df.begin(), df.end()) - df.begin());
  vector<int> path;
  int cur = other;
  path.push_back(cur);
  while (cur != far) {
    for (int next : adjacency[cur]) {
      if (df[next] == df[cur] - 1) {
        cur = next;
        path.push_back(cur);
        break;
      }
    }
  }
  int midpoint = path[path.size() / 2];
  auto [mid_ecc, mid_reached] = bfs(midpoint, -1);
  (void)mid_reached;
  int best = mid_ecc;
  int best_source = midpoint;

  for (int source : sources) {
    auto [eccentricity, source_reached] = bfs(source, best);
    if (source_reached > 0 && eccentricity < best) {
      best = eccentricity;
      best_source = source;
    }
  }
  answer.radius = best;
  answer.centre_code = code[best_source];
  return answer;
}

static Graph base_example() {
  // Official graph6 string: IsLR?KIB?.  Edge list copied here to avoid any
  // dependency on a graph6 parser.
  return Graph(10, {{0, 1}, {0, 2}, {0, 3}, {1, 5}, {1, 6},
                    {2, 4}, {2, 6}, {3, 4}, {3, 5}, {4, 8},
                    {4, 9}, {5, 7}, {5, 9}, {6, 7}, {6, 8}});
}

static Graph toggle_edge(const Graph& g, int a, int b) {
  vector<pair<int, int>> edges;
  for (auto edge : g.edges) {
    if (edge != pair<int, int>{a, b}) edges.push_back(edge);
  }
  if (!g.has_edge(a, b)) edges.push_back({a, b});
  return Graph(g.n, std::move(edges));
}

static Graph parse_graph6(string line) {
  if (!line.empty() && line.back() == '\r') line.pop_back();
  if (line.rfind(">>graph6<<", 0) == 0) line.erase(0, 10);
  if (line.empty() || static_cast<unsigned char>(line[0]) == 126) {
    cerr << "only short graph6 records (n <= 62) are supported\n";
    std::exit(2);
  }
  for (unsigned char byte : line) {
    if (byte < 63 || byte > 126) {
      cerr << "invalid byte in graph6 record\n";
      std::exit(2);
    }
  }
  int n = int(static_cast<unsigned char>(line[0])) - 63;
  int edge_bits = n * (n - 1) / 2;
  size_t expected_length = 1 + size_t((edge_bits + 5) / 6);
  if (line.size() != expected_length) {
    cerr << "noncanonical graph6 record length\n";
    std::exit(2);
  }
  int remainder = edge_bits % 6;
  if (remainder != 0) {
    int padding_bits = 6 - remainder;
    int last_word = int(static_cast<unsigned char>(line.back())) - 63;
    if ((last_word & ((1 << padding_bits) - 1)) != 0) {
      cerr << "nonzero graph6 padding\n";
      std::exit(2);
    }
  }
  vector<pair<int, int>> edges;
  size_t position = 1;
  int bits_left = 0;
  int word = 0;
  auto bit = [&]() {
    if (bits_left == 0) {
      if (position >= line.size()) {
        cerr << "truncated graph6 record\n";
        std::exit(2);
      }
      word = int(static_cast<unsigned char>(line[position++])) - 63;
      bits_left = 6;
    }
    int value = (word >> (--bits_left)) & 1;
    return value;
  };
  // graph6 orders upper-triangle bits column by column:
  // (0,1), (0,2),(1,2), (0,3),(1,3),(2,3), ...
  for (int v = 1; v < n; ++v) {
    for (int u = 0; u < v; ++u) {
      if (bit()) edges.push_back({u, v});
    }
  }
  return Graph(n, std::move(edges));
}

static void print_result(const string& label, const Result& r) {
  cout << label << " connected=" << r.connected << " radius=" << r.radius
       << " states=" << r.states << " colour_orbits=" << r.orbit_representatives
       << " centre_code=" << r.centre_code << '\n';
}

static void print_json_array(const std::array<long long, 8>& values) {
  cout << '[';
  for (size_t index = 0; index < values.size(); ++index) {
    if (index != 0) cout << ',';
    cout << values[index];
  }
  cout << ']';
}

static int verify_atlas(const string& path) {
  std::ifstream input(path);
  if (!input) {
    cerr << "could not open graph6 atlas: " << path << '\n';
    return 2;
  }

  std::array<long long, 8> records{};
  std::array<long long, 8> c3_connected{};
  std::array<long long, 8> eligible{};
  long long counterexamples = 0;
  std::set<string> seen;
  string line;
  while (std::getline(input, line)) {
    if (!line.empty() && line.back() == '\r') line.pop_back();
    if (line.empty()) {
      cerr << "blank graph6 record in fixed atlas\n";
      return 2;
    }
    if (!seen.insert(line).second) {
      cerr << "duplicate graph6 record in fixed atlas: " << line << '\n';
      return 2;
    }
    Graph graph = parse_graph6(line);
    if (graph.n < 1 || graph.n > 7) {
      cerr << "fixed atlas contains graph of unsupported order " << graph.n << '\n';
      return 2;
    }
    ++records[graph.n];

    Result r3 = exact_radius(graph, 3);
    if (!r3.connected) continue;
    ++c3_connected[graph.n];
    Result r4 = exact_radius(graph, 4);
    if (!r4.connected) continue;
    ++eligible[graph.n];
    if (r3.radius < r4.radius) {
      ++counterexamples;
      cerr << "COUNTEREXAMPLE graph6=" << line << " n=" << graph.n
           << " m=" << graph.edges.size() << " radii=" << r3.radius << ','
           << r4.radius << '\n';
    }
  }
  if (!input.eof()) {
    cerr << "failed while reading graph6 atlas\n";
    return 2;
  }

  cout << "{\"records_by_order\":";
  print_json_array(records);
  cout << ",\"c3_connected_by_order\":";
  print_json_array(c3_connected);
  cout << ",\"eligible_by_order\":";
  print_json_array(eligible);
  cout << ",\"counterexamples\":" << counterexamples << "}\n";
  return counterexamples == 0 ? 0 : 1;
}

int main(int argc, char** argv) {
  string mode = argc >= 2 ? argv[1] : "base";
  if (mode == "verify-atlas") {
    if (argc != 3) {
      cerr << "usage: recolor_radius_exact verify-atlas ATLAS.g6\n";
      return 2;
    }
    return verify_atlas(argv[2]);
  }
  Graph base = base_example();
  if (mode == "base") {
    Result r3 = exact_radius(base, 3);
    Result r4 = exact_radius(base, 4);
    print_result("base k=3", r3);
    print_result("base k=4", r4);
    return 0;
  }
  if (mode == "stream") {
    int shard = argc >= 3 ? std::stoi(argv[2]) : 0;
    int shards = argc >= 4 ? std::stoi(argv[3]) : 1;
    string line;
    long long index = 0;
    long long tested = 0;
    long long connected_pairs = 0;
    while (std::getline(std::cin, line)) {
      long long current = index++;
      if (current % shards != shard) continue;
      Graph g = parse_graph6(line);
      Result r3 = exact_radius(g, 3);
      if (!r3.connected) continue;
      Result r4 = exact_radius(g, 4);
      ++tested;
      if (!r4.connected) continue;
      ++connected_pairs;
      if (r3.radius < r4.radius) {
        cout << "COUNTEREXAMPLE graph6=" << line << " n=" << g.n
             << " m=" << g.edges.size() << " radii=" << r3.radius << ','
             << r4.radius << " states=" << r3.states << ',' << r4.states
             << " centres=" << r3.centre_code << ',' << r4.centre_code
             << " edges=";
        for (auto [u, v] : g.edges) cout << u << '-' << v << ',';
        cout << '\n' << std::flush;
      }
      if (tested % 250 == 0) {
        cerr << "shard=" << shard << " records=" << (current + 1)
             << " tested=" << tested << " connected_pairs=" << connected_pairs
             << '\n';
      }
    }
    cerr << "DONE shard=" << shard << " records=" << index << " tested="
         << tested << " connected_pairs=" << connected_pairs << '\n';
    return 0;
  }
  if (mode != "toggle") {
    cerr << "usage: recolor_radius_exact "
            "[base|toggle|stream [shard shards]|verify-atlas ATLAS.g6]\n";
    return 2;
  }
  int shard = argc >= 3 ? std::stoi(argv[2]) : 0;
  int shards = argc >= 4 ? std::stoi(argv[3]) : 1;
  int index = 0;
  for (int a = 0; a < base.n; ++a) {
    for (int b = a + 1; b < base.n; ++b, ++index) {
      if (index % shards != shard) continue;
      Graph g = toggle_edge(base, a, b);
      Result r3 = exact_radius(g, 3);
      cout << "toggle=" << a << ',' << b << " edge_now=" << g.has_edge(a, b)
           << ' ';
      print_result("k=3", r3);
      if (!r3.connected) continue;
      Result r4 = exact_radius(g, 4);
      cout << "toggle=" << a << ',' << b << " edge_now=" << g.has_edge(a, b)
           << ' ';
      print_result("k=4", r4);
      if (r4.connected && r3.radius < r4.radius) {
        cout << "COUNTEREXAMPLE toggle=" << a << ',' << b << " radii="
             << r3.radius << ',' << r4.radius << " edges=";
        for (auto [u, v] : g.edges) cout << u << '-' << v << ',';
        cout << '\n';
      }
    }
  }
  return 0;
}
