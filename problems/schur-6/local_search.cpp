#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <random>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

struct Triple {
    int a, b, c;
    int weight = 1;
    bool bad = false;
};

struct Move {
    int vertex = -1;
    int color = -1;
    long long weighted_delta = std::numeric_limits<long long>::max();
    int raw_delta = std::numeric_limits<int>::max();
};

struct Options {
    int maximum = 537;
    int colors = 6;
    int restarts = 1000000;
    std::uint64_t steps = 1000000000ULL;
    double seconds = 60.0;
    std::uint64_t seed = 1;
    int perturb = 8;
    double noise = 0.025;
    std::string seed_file;
    std::string output;
};

static Options parse_options(int argc, char** argv) {
    Options result;
    for (int i = 1; i < argc; ++i) {
        const std::string key = argv[i];
        auto value = [&]() -> std::string {
            if (++i >= argc) throw std::runtime_error("missing value for " + key);
            return argv[i];
        };
        if (key == "--maximum") result.maximum = std::stoi(value());
        else if (key == "--colors") result.colors = std::stoi(value());
        else if (key == "--restarts") result.restarts = std::stoi(value());
        else if (key == "--steps") result.steps = std::stoull(value());
        else if (key == "--seconds") result.seconds = std::stod(value());
        else if (key == "--seed") result.seed = std::stoull(value());
        else if (key == "--perturb") result.perturb = std::stoi(value());
        else if (key == "--noise") result.noise = std::stod(value());
        else if (key == "--seed-file") result.seed_file = value();
        else if (key == "--output") result.output = value();
        else throw std::runtime_error("unknown option: " + key);
    }
    if (result.maximum < 2 || result.colors < 2 || result.restarts < 1 ||
        result.steps < 1 || result.seconds <= 0.0 ||
        result.noise < 0.0 || result.noise > 1.0) {
        throw std::runtime_error("invalid option value");
    }
    return result;
}

static std::vector<int> read_seed(const std::string& path, int maximum,
                                  int expected_colors) {
    std::vector<int> color(maximum + 1, -1);
    if (path.empty()) return color;
    std::ifstream input(path);
    if (!input) throw std::runtime_error("cannot open seed file: " + path);
    std::string line;
    int row = 0;
    while (std::getline(input, line)) {
        const auto comment = line.find('#');
        if (comment != std::string::npos) line.resize(comment);
        std::istringstream parser(line);
        std::vector<int> values;
        int value;
        while (parser >> value) values.push_back(value);
        if (values.empty()) continue;
        if (row >= expected_colors) throw std::runtime_error("too many seed rows");
        for (int v : values) {
            if (v < 1 || v > maximum) throw std::runtime_error("seed value out of range");
            if (color[v] != -1) throw std::runtime_error("duplicate seed value");
            color[v] = row;
        }
        ++row;
    }
    if (row != expected_colors) throw std::runtime_error("wrong number of seed rows");
    return color;
}

class Search {
public:
    explicit Search(const Options& options)
        : opt(options), rng(options.seed), color(options.maximum + 1, -1),
          base_color(read_seed(options.seed_file, options.maximum, options.colors)),
          incident(options.maximum + 1), tabu(options.maximum + 1,
              std::vector<std::uint64_t>(options.colors, 0)) {
        for (int a = 1; a <= opt.maximum; ++a) {
            for (int b = a; a + b <= opt.maximum; ++b) {
                const int index = static_cast<int>(triples.size());
                triples.push_back({a, b, a + b, 1, false});
                incident[a].push_back(index);
                if (b != a) incident[b].push_back(index);
                incident[a + b].push_back(index);
            }
        }
        position.assign(triples.size(), -1);
    }

    bool run() {
        const auto started = std::chrono::steady_clock::now();
        std::uint64_t total_steps = 0;
        int global_best = std::numeric_limits<int>::max();
        std::vector<int> global_best_color;

        for (int restart = 0; restart < opt.restarts; ++restart) {
            initialize(restart);
            if (raw_score < global_best) {
                global_best = raw_score;
                global_best_color = color;
                write_solution(global_best_color);
                report(restart, total_steps, global_best, started);
            }
            for (std::uint64_t local_step = 0;
                 local_step < opt.steps; ++local_step, ++total_steps) {
                if (raw_score == 0) {
                    write_solution(color);
                    report(restart, total_steps, 0, started);
                    return true;
                }
                if ((total_steps & 8191ULL) == 0 && elapsed(started) >= opt.seconds) {
                    write_solution(global_best_color);
                    std::cerr << "TIMEOUT best=" << global_best
                              << " steps=" << total_steps
                              << " seconds=" << elapsed(started) << '\n';
                    return false;
                }

                const int conflict = violated[random_index(violated.size())];
                Move move = best_move(conflict, total_steps, global_best);
                if (move.vertex < 0) move = best_move(conflict, total_steps, global_best, true);

                const bool local_minimum = move.weighted_delta >= 0;
                if (local_minimum) {
                    for (int index : violated) {
                        ++triples[index].weight;
                        ++weighted_score;
                    }
                    move = best_move(conflict, total_steps, global_best, true);
                }

                if (uniform01() < opt.noise) {
                    move = random_move(conflict);
                }
                const int old_color = color[move.vertex];
                apply_move(move.vertex, move.color);
                const std::uint64_t tenure = 7 + random_index(13) + violated.size() / 35;
                tabu[move.vertex][old_color] = total_steps + tenure;

                if (raw_score < global_best) {
                    global_best = raw_score;
                    global_best_color = color;
                    write_solution(global_best_color);
                    report(restart, total_steps, global_best, started);
                }
                if (local_step > 0 && local_step % 100000 == 0) decay_weights();
            }
        }
        std::cerr << "EXHAUSTED best=" << global_best
                  << " steps=" << total_steps << '\n';
        write_solution(global_best_color);
        return false;
    }

private:
    const Options opt;
    std::mt19937_64 rng;
    std::vector<int> color;
    const std::vector<int> base_color;
    std::vector<Triple> triples;
    std::vector<std::vector<int>> incident;
    std::vector<int> violated;
    std::vector<int> position;
    std::vector<std::vector<std::uint64_t>> tabu;
    int raw_score = 0;
    long long weighted_score = 0;

    std::size_t random_index(std::size_t n) {
        return std::uniform_int_distribution<std::size_t>(0, n - 1)(rng);
    }
    double uniform01() {
        return std::uniform_real_distribution<double>(0.0, 1.0)(rng);
    }
    static double elapsed(const std::chrono::steady_clock::time_point& started) {
        return std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count();
    }

    bool monochromatic(const Triple& t) const {
        return color[t.a] == color[t.b] && color[t.a] == color[t.c];
    }
    bool monochromatic_after(const Triple& t, int vertex, int new_color) const {
        const int ca = t.a == vertex ? new_color : color[t.a];
        const int cb = t.b == vertex ? new_color : color[t.b];
        const int cc = t.c == vertex ? new_color : color[t.c];
        return ca == cb && ca == cc;
    }

    void set_bad(int index, bool bad) {
        Triple& t = triples[index];
        if (t.bad == bad) return;
        t.bad = bad;
        if (bad) {
            position[index] = static_cast<int>(violated.size());
            violated.push_back(index);
        } else {
            const int at = position[index];
            const int last = violated.back();
            violated[at] = last;
            position[last] = at;
            violated.pop_back();
            position[index] = -1;
        }
    }

    void initialize(int restart) {
        color = base_color;
        for (int value = 1; value <= opt.maximum; ++value) {
            if (color[value] < 0) color[value] = static_cast<int>(random_index(opt.colors));
        }
        int changes = restart == 0 ? 0 : opt.perturb * (1 + (restart % 12));
        if (restart > 0 && restart % 13 == 0) changes = opt.maximum;
        for (int i = 0; i < changes; ++i) {
            const int value = 1 + static_cast<int>(random_index(opt.maximum));
            int replacement = static_cast<int>(random_index(opt.colors - 1));
            if (replacement >= color[value]) ++replacement;
            color[value] = replacement;
        }
        violated.clear();
        std::fill(position.begin(), position.end(), -1);
        for (Triple& t : triples) {
            t.weight = 1;
            t.bad = false;
        }
        raw_score = 0;
        weighted_score = 0;
        for (int index = 0; index < static_cast<int>(triples.size()); ++index) {
            if (monochromatic(triples[index])) {
                set_bad(index, true);
                ++raw_score;
                ++weighted_score;
            }
        }
        for (auto& row : tabu) std::fill(row.begin(), row.end(), 0);
    }

    Move evaluate(int vertex, int new_color) const {
        Move result{vertex, new_color, 0, 0};
        for (int index : incident[vertex]) {
            const Triple& t = triples[index];
            const bool after = monochromatic_after(t, vertex, new_color);
            if (after != t.bad) {
                const int direction = after ? 1 : -1;
                result.raw_delta += direction;
                result.weighted_delta += static_cast<long long>(direction) * t.weight;
            }
        }
        return result;
    }

    std::vector<int> vertices_of(const Triple& t) const {
        if (t.a == t.b) return {t.a, t.c};
        return {t.a, t.b, t.c};
    }

    Move best_move(int conflict, std::uint64_t step, int global_best,
                   bool ignore_tabu = false) {
        std::vector<Move> best;
        long long best_delta = std::numeric_limits<long long>::max();
        for (int vertex : vertices_of(triples[conflict])) {
            for (int replacement = 0; replacement < opt.colors; ++replacement) {
                if (replacement == color[vertex]) continue;
                Move candidate = evaluate(vertex, replacement);
                const bool aspiration = raw_score + candidate.raw_delta < global_best;
                if (!ignore_tabu && tabu[vertex][replacement] > step && !aspiration) continue;
                if (candidate.weighted_delta < best_delta) {
                    best_delta = candidate.weighted_delta;
                    best.assign(1, candidate);
                } else if (candidate.weighted_delta == best_delta) {
                    best.push_back(candidate);
                }
            }
        }
        if (best.empty()) return Move{};
        return best[random_index(best.size())];
    }

    Move random_move(int conflict) {
        const std::vector<int> vertices = vertices_of(triples[conflict]);
        const int vertex = vertices[random_index(vertices.size())];
        int replacement = static_cast<int>(random_index(opt.colors - 1));
        if (replacement >= color[vertex]) ++replacement;
        return evaluate(vertex, replacement);
    }

    void apply_move(int vertex, int new_color) {
        for (int index : incident[vertex]) {
            Triple& t = triples[index];
            const bool after = monochromatic_after(t, vertex, new_color);
            if (after != t.bad) {
                const int direction = after ? 1 : -1;
                raw_score += direction;
                weighted_score += static_cast<long long>(direction) * t.weight;
                set_bad(index, after);
            }
        }
        color[vertex] = new_color;
    }

    void decay_weights() {
        weighted_score = 0;
        for (Triple& t : triples) {
            t.weight = std::max(1, (t.weight + 1) / 2);
            if (t.bad) weighted_score += t.weight;
        }
    }

    void write_solution(const std::vector<int>& solution) const {
        if (opt.output.empty()) return;
        std::ofstream out(opt.output);
        if (!out) throw std::runtime_error("cannot create output file: " + opt.output);
        for (int c = 0; c < opt.colors; ++c) {
            bool first = true;
            for (int value = 1; value <= opt.maximum; ++value) {
                if (solution[value] == c) {
                    if (!first) out << ' ';
                    out << value;
                    first = false;
                }
            }
            out << '\n';
        }
    }

    static void report(int restart, std::uint64_t steps, int best,
                       const std::chrono::steady_clock::time_point& started) {
        std::cerr << "IMPROVED best=" << best << " restart=" << restart
                  << " steps=" << steps << " seconds=" << elapsed(started) << '\n';
    }
};

int main(int argc, char** argv) {
    try {
        const Options options = parse_options(argc, argv);
        Search search(options);
        return search.run() ? 0 : 2;
    } catch (const std::exception& error) {
        std::cerr << "ERROR: " << error.what() << '\n';
        return 1;
    }
}
