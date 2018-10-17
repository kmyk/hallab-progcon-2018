#include <algorithm>
#include <bitset>
#include <cassert>
#include <climits>
#include <functional>
#include <iostream>
#include <memory>
#include <numeric>
#include <random>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include "Answer.hpp"
#define REP(i, n) for (int i = 0; (i) < (int)(n); ++ (i))
#define REP3(i, m, n) for (int i = (m); (i) < (int)(n); ++ (i))
#define REP_R(i, n) for (int i = int(n) - 1; (i) >= 0; -- (i))
#define REP3R(i, m, n) for (int i = int(n) - 1; (i) >= (int)(m); -- (i))
#define ALL(x) begin(x), end(x)
typedef long long ll;
template <class T, class U> inline void chmax(T & a, U const & b) { a = std::max<T>(a, b); }
template <class T, class U> inline void chmin(T & a, U const & b) { a = std::min<T>(a, b); }

//------------------------------------------------------------------------------
namespace hpc {

using namespace std;

constexpr int H = Parameter::OvenHeight;
constexpr int W = Parameter::OvenWidth;
constexpr int K = Parameter::CandidatePieceCount;

bool is_on_oven(int y, int x) {
    return 0 <= y and y < H and 0 <= x and x < W;
}

template <class RandomAccessIterator, class RandomEngine>
auto sample1(RandomAccessIterator first, RandomAccessIterator last, RandomEngine & gen) -> decltype(*first) {
    assert (first != last);
    int i = uniform_int_distribution<int>(0, distance(first, last) - 1)(gen);
    return *(first + i);
}

class xor_shift_128 {
public:
    typedef uint32_t result_type;
    xor_shift_128(uint32_t seed = 42) {
        set_seed(seed);
    }
    void set_seed(uint32_t seed) {
        a = seed = 1812433253u * (seed ^ (seed >> 30));
        b = seed = 1812433253u * (seed ^ (seed >> 30)) + 1;
        c = seed = 1812433253u * (seed ^ (seed >> 30)) + 2;
        d = seed = 1812433253u * (seed ^ (seed >> 30)) + 3;
    }
    uint32_t operator() () {
        uint32_t t = (a ^ (a << 11));
        a = b; b = c; c = d;
        return d = (d ^ (d >> 19)) ^ (t ^ (t >> 8));
    }
    static constexpr uint32_t max() { return numeric_limits<result_type>::max(); }
    static constexpr uint32_t min() { return numeric_limits<result_type>::min(); }
private:
    uint32_t a, b, c, d;
};

typedef array<uint32_t, Parameter::OvenHeight> packed_oven_t;
packed_oven_t pack_oven(Oven const & oven) {
    static_assert (Parameter::OvenWidth < CHAR_BIT * sizeof(uint32_t), "");
    packed_oven_t a = {};
    REP (y, Parameter::OvenHeight) {
        REP (x, Parameter::OvenWidth) {
            if (oven.isAbleToPut(1, 1, Vector2i(x, y))) {
                a[y] |= 1u << x;
            }
        }
    }
    return a;
}

Piece const & get_piece_from_action(Stage const & stage, Action const & action) {
    return stage.candidateLane(action.candidateLaneType()).pieces()[action.pieceIndex()];
}

bool is_intersect(Vector2i const & pos1, Piece const & piece1, Vector2i const & pos2, Piece const & piece2) {
    return Util::IsIntersect(
        pos1, piece1.width(), piece1.height(),
        pos2, piece2.width(), piece2.height());
}

template <typename Func>
void iterate_all_puttable_pos(Oven const & oven, Piece const & piece, Func func) {
    array<array<char, W + 1>, H + 1> imos = {};
    for (auto const & baking : oven.bakingPieces()) {
        int ly = baking.pos().y;
        int lx = baking.pos().x;
        int ry = ly + baking.height();
        int rx = lx + baking.width();
        ly = max(0, ly - piece.height() + 1);
        lx = max(0, lx - piece.width() + 1);
        imos[ly][lx] += 1;
        imos[ly][rx] -= 1;
        imos[ry][lx] -= 1;
        imos[ry][rx] += 1;
    }
    REP (y, H - piece.height() + 1) {
        REP (x, W - piece.width() + 1) {
            imos[y    ][x + 1] += imos[y][x];
            imos[y + 1][x    ] += imos[y][x];
            imos[y + 1][x + 1] -= imos[y][x];
            if (not imos[y][x]) {
                func(Vector2i(x, y));
            }
        }
    }
}

bool operator == (Action const & a, Action const & b) {
    if (a.isWaiting() or b.isWaiting()) {
        return a.isWaiting() == b.isWaiting();
    } else {
        return make_tuple(a.candidateLaneType(), a.pieceIndex(), a.putPos())
            == make_tuple(b.candidateLaneType(), b.pieceIndex(), b.putPos());
    }
}
bool operator != (Action const & a, Action const & b) {
    return not (a == b);
}

void fill_rest_hest_turn(Oven const & oven, array<array<int16_t, W>, H> & rest_heat_turn) {
    REP (y, H) REP (x, W) rest_heat_turn[y][x] = 0;
    for (auto const & piece : oven.bakingPieces()) {
        int ly = piece.pos().y;
        int lx = piece.pos().x;
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        int16_t t = piece.restRequiredHeatTurnCount();
        REP3 (y, ly, ry) REP3 (x, lx, rx) {
            rest_heat_turn[y][x] = t;
        }
    }
}

CandidateLaneType get_candidate_lane_type(int i) {
    assert (0 <= i and i < 2 * K);
    return i < K ? CandidateLaneType_Small : CandidateLaneType_Large;
}
Piece const & get_piece(Stage const & stage, int i) {
    assert (0 <= i and i < 2 * K);
    return stage.candidateLane(get_candidate_lane_type(i)).pieces()[i % K];
}

void fill_puttable_t(Stage const & stage, array<array<array<int16_t, W>, H>, 2 * K> & puttable_t) {
    // TODO: O(KHWb) から O(Kb + KHW) にできる
    // TODO: uint8_t でよくないか
    REP (i, 2 * K) {
        auto const & piece = get_piece(stage, i);
        REP (y, H) REP (x, W) puttable_t[i][y][x] = INT16_MAX;
        if (stage.turn() + piece.requiredHeatTurnCount() >= Parameter::GameTurnLimit) continue;
        REP (y, H - piece.height() + 1) REP (x, W - piece.width() + 1) {
            puttable_t[i][y][x] = 0;
            for (auto const & baking : stage.oven().bakingPieces()) {
                if (is_intersect(Vector2i(x, y), piece, baking.pos(), baking)) {
                    chmax(puttable_t[i][y][x], baking.restRequiredHeatTurnCount() + 1);
                }
            }
        }
    }
}

void list_puttable_pos(Stage const & stage, array<array<array<int16_t, W>, H>, 2 * K> const & puttable_t, int DEPTH, array<vector<pair<int8_t, int8_t> >, 2 * K> & puttable_pos) {
    REP (i, 2 * K) {
        puttable_pos[i].clear();
        REP (y, H) REP (x, W) {
            if (puttable_t[i][y][x] < DEPTH) {
                puttable_pos[i].emplace_back(y, x);
            }
        }
    }
}

vector<pair<int, Action> > do_simulated_annealing(Stage const & stage, vector<pair<int, Action> > const & hint) {
    constexpr int DEPTH = 20;
#ifdef LOCAL
    random_device device;
    static xor_shift_128 gen((device()));
#else
    static xor_shift_128 gen;
#endif

    static array<array<int16_t, W>, H> rest_heat_turn;
    fill_rest_hest_turn(stage.oven(), rest_heat_turn);

    static array<array<array<int16_t, W>, H>, 2 * K> puttable_t;
    fill_puttable_t(stage, puttable_t);

    static array<vector<pair<int8_t, int8_t> >, 2 * K> puttable_pos;
    list_puttable_pos(stage, puttable_t, DEPTH, puttable_pos);

    vector<int> puttable_i;
    REP (i, 2 * K) if (not puttable_pos[i].empty()) {
        puttable_i.push_back(i);
    }
    if (puttable_i.empty()) {
        return vector<pair<int, Action> >();
    }

    auto get_score_delta_one = [&](array<pair<int, Action>, 2 * K> const & cur, array<array<int8_t, H>, W> const & used, array<int, 2 * K> const & updated, int i, int t0, int ly, int lx) {
        auto const & piece = get_piece(stage, i);
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        int t = piece.requiredHeatTurnCount();
        auto touch = [&](int y, int x) -> double {
            if (not is_on_oven(y, x)) return t;
            double acc = 0;
            if (rest_heat_turn[y][x]) {
                acc += max(0, min<int>(rest_heat_turn[y][x], t + t0) - t0);
            }
            int j = used[y][x];
            if (j != -1 and updated[j] != -1) {
                auto const & piece_ = get_piece(stage, j);
                int t0_ = updated[j];
                int t_ = piece_.requiredHeatTurnCount();
                int a = max(0, min(t0 + t, t0_ + t_) - max(t0, t0_));
                acc += pow(0.9, max(t0, t0_) - t0) * a;
            }
            return acc;
        };
        double score = 0;
        if (lx == 0) score += t * (ry - ly);
        if (lx != 0) REP3 (y, ly, ry) touch(y, lx - 1);
        if (ly == 0) score += t * (rx - lx);
        if (ly != 0) REP3 (x, lx, rx) touch(ly - 1, x);
        if (rx == W) score += t * (ry - ly);
        if (rx != W) REP3 (y, ly, ry) touch(y, rx);
        if (ry == H) score += t * (rx - lx);
        if (ry != H) REP3 (x, lx, rx) touch(ry, x);
        return pow(0.9, t0) * pow(piece.height() * piece.width(), 1.1) * 100 + pow(0.9, t0) * score;
    };

// -Werror 付けるのやめてほしい
#ifdef LOCAL
    auto get_score_delta_unput = [&](array<pair<int, Action>, 2 * K> const & cur, array<array<int8_t, H>, W> const & used, int i) {
        assert (cur[i].first != -1);
        array<int, 2 * K> updated;
        REP (j, 2 * K) updated[j] = cur[j].first;
        auto const & pos = cur[i].second.putPos();
        return - get_score_delta_one(cur, used, updated, i, updated[i], pos.y, pos.x);
    };
#endif

    auto get_score_delta_put = [&](array<pair<int, Action>, 2 * K> const & cur, array<array<int8_t, H>, W> const & used, int i, int t0, int y, int x) {
        assert (puttable_t[i][y][x] <= t0);
        array<int, 2 * K> updated;
        REP (j, 2 * K) updated[j] = cur[j].first;
        array<int, 2 * K> order;
        iota(ALL(order), 0);
        sort(ALL(order), [&](int j1, int j2) { return updated[j1] < updated[j2]; });

        double score = 0;
        set<int> used_t0;
        used_t0.insert(t0);
        auto const & piece = get_piece(stage, i);
        for (int j : order) {
            if (updated[j] == -1) continue;
            auto const & action = cur[j].second;
            if (j == i or is_intersect(Vector2i(x, y), piece, action.putPos(), get_piece_from_action(stage, action))) {
                score -= get_score_delta_one(cur, used, updated, j, updated[j], action.putPos().y, action.putPos().x);
                updated[j] = -1;
                continue;
            }
            if (used_t0.count(updated[j])) {
                score -= get_score_delta_one(cur, used, updated, j, updated[j], action.putPos().y, action.putPos().x);
                while (used_t0.count(updated[j])) ++ updated[j];
                score += get_score_delta_one(cur, used, updated, j, updated[j], action.putPos().y, action.putPos().x);
            }
            used_t0.insert(updated[j]);
        }
        score += get_score_delta_one(cur, used, updated, i, t0, y, x);
        return score;
    };

    auto does_conflict = [&](array<pair<int, Action>, 2 * K> & cur, array<array<int8_t, H>, W> & used, int i, int t0, int ly, int lx) {
        auto const & piece = get_piece(stage, i);
        REP (j, 2 * K) {
            int & t0_ = cur[j].first;
            if (t0_ == -1) continue;
            auto const & action = cur[j].second;
            if (j == i or is_intersect(Vector2i(lx, ly), piece, action.putPos(), get_piece_from_action(stage, action))) {
                return true;
            }
        }
        return false;
    };


    auto unput = [&](array<pair<int, Action>, 2 * K> & cur, array<array<int8_t, H>, W> & used, int i) {
        auto const & piece = get_piece(stage, i);
        int ly = cur[i].second.putPos().y;
        int lx = cur[i].second.putPos().x;
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        REP3 (y, ly, ry) REP3 (x, lx, rx) {
            used[y][x] = -1;
        }
        cur[i].first = -1;
    };

    auto put = [&](array<pair<int, Action>, 2 * K> & cur, array<array<int8_t, H>, W> & used, int i, int t0, int ly, int lx) {
        assert (puttable_t[i][ly][lx] <= t0);
        array<int, 2 * K> order;
        iota(ALL(order), 0);
        sort(ALL(order), [&](int j1, int j2) { return cur[j1].first < cur[j2].first; });

        set<int> used_t0;
        used_t0.insert(t0);
        auto const & piece = get_piece(stage, i);
        for (int j : order) {
            int & t0_ = cur[j].first;
            if (t0_ == -1) continue;
            auto const & action = cur[j].second;
            if (j == i or is_intersect(Vector2i(lx, ly), piece, action.putPos(), get_piece_from_action(stage, action))) {
                unput(cur, used, j);
                t0_ = -1;
                continue;
            }
            while (used_t0.count(t0_)) ++ t0_;
            used_t0.insert(t0_);
        }
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        REP3 (y, ly, ry) REP3 (x, lx, rx) {
            used[y][x] = i;
        }
        cur[i].first = t0;
        cur[i].second = Action::Put(get_candidate_lane_type(i), i % K, Vector2i(lx, ly));
    };

    array<pair<int, Action>, 2 * K> cur;
    fill(ALL(cur), make_pair(-1, Action::Wait()));
    double score = 0;
    array<array<int8_t, H>, W> used;
    REP (y, H) REP (x, W) used[y][x] = -1;

    vector<int> placed_small, placed_large;
    set<int> used_t0;

    for (auto const & it : hint) {
        int t0 = it.first - stage.turn();
        assert (t0 >= 0);
        auto const & action = it.second;
        auto const & piece = stage.candidateLane(action.candidateLaneType()).pieces()[action.pieceIndex()];
        if (stage.turn() + piece.requiredHeatTurnCount() >= Parameter::GameTurnLimit) continue;
        int i = (action.candidateLaneType() == CandidateLaneType_Small ? 0 : 8) + action.pieceIndex();
        int y = action.putPos().y;
        int x = action.putPos().x;
        assert (puttable_t[i][y][x] <= t0);
        score += get_score_delta_put(cur, used, i, t0, y, x);
        put(cur, used, i, t0, y, x);
        (i < K ? placed_small : placed_large).push_back(i);
        used_t0.insert(t0);
    }

    auto result = cur;
    auto highscore = score;
    constexpr int ITERATION = 1000;
    REP (iteration, ITERATION) {
        auto use = [&](int i, int t0, int y, int x) {
            assert (puttable_t[i][y][x] <= t0);
            auto delta = get_score_delta_put(cur, used, i, t0, y, x);
            double temperature = (double)(ITERATION - iteration) / ITERATION;
            double BOLTZMANN = 0.001;
            if (0 <= delta or bernoulli_distribution(exp(BOLTZMANN * delta) * temperature)(gen)) {
                score += delta;
                put(cur, used, i, t0, y, x);
                placed_small.clear();
                placed_large.clear();
                used_t0 = set<int>();
                REP (j, 2 * K) if (cur[j].first != -1) {
                    (j < K ? placed_small : placed_large).push_back(j);
                    used_t0.insert(cur[j].first);
                }
                if (highscore < score) {
                    highscore = score;
                    result = cur;
                }
                return true;
            }
            return false;
        };


        double prob = uniform_real_distribution<double>()(gen);
        auto const & placed = (iteration % 5 == 0 ? placed_small : placed_large);
        if (prob < 0.1 and not placed.empty()) {
            int i = sample1(ALL(placed), gen);
            int y = cur[i].second.putPos().y;
            int x = cur[i].second.putPos().x;
            int t0 = cur[i].first;
            if (t0 == puttable_t[i][y][x]) continue;
            int k = uniform_int_distribution<int>(1, 3)(gen);
            t0 = max(0, t0 - k);
            if (t0 < puttable_t[i][y][x]) continue;
            use(i, t0, y, x);

        } else if (prob < 0.3 and not placed.empty()) {
            int i = sample1(ALL(placed), gen);
            int y = cur[i].second.putPos().y;
            int x = cur[i].second.putPos().x;
            int dir = uniform_int_distribution<int>(0, 3)(gen);
            while (true) {
                switch (dir) {
                    case 0: -- y; break;
                    case 1: ++ y; break;
                    case 2: ++ x; break;
                    case 3: -- x; break;
                }
                if (not is_on_oven(y, x)) break;
                if (puttable_t[i][y][x] == INT16_MAX) break;
                int t0 = max<int>(puttable_t[i][y][x], cur[i].first - 1);
                use(i, t0, y, x);
                ++ iteration;
            }


        } else if (prob < 0.6 and not placed.empty()) {
            int dir = uniform_int_distribution<int>(0, 3)(gen);
            vector<pair<int, int> > order;
            for (int i : placed) {
                int y = cur[i].second.putPos().y;
                int x = cur[i].second.putPos().x;
                switch (dir) {
                    case 0: order.emplace_back(- y, i); break;
                    case 1: order.emplace_back(+ y, i); break;
                    case 2: order.emplace_back(+ x, i); break;
                    case 3: order.emplace_back(- x, i); break;
                }
            }
            sort(ALL(order));

            array<pair<int, Action>, 2 * K> nxt;
            fill(ALL(nxt), make_pair(-1, Action::Wait()));
            double next_score = 0;
            array<array<int8_t, H>, W> next_used;
            REP (y, H) REP (x, W) next_used[y][x] = -1;

            for (auto it : order) {
                int i = it.second;
                int t0 = cur[i].first;
                int y = cur[i].second.putPos().y;
                int x = cur[i].second.putPos().x;
                while (true) {
                    int ny = y;
                    int nx = x;
                    switch (dir) {
                        case 0: -- ny; break;
                        case 1: ++ ny; break;
                        case 2: ++ nx; break;
                        case 3: -- nx; break;
                    }
                    if (not is_on_oven(ny, nx)) break;
                    if (t0 < puttable_t[i][ny][nx]) break;
                    if (does_conflict(nxt, next_used, i, t0, ny, nx)) break;
                    y = ny;
                    x = nx;
                }
                next_score += get_score_delta_put(nxt, next_used, i, t0, y, x);
                put(nxt, next_used, i, t0, y, x);
            }
            auto delta = next_score - score;
            double temperature = (double)(ITERATION - iteration) / ITERATION;
            double BOLTZMANN = 0.001;
            if (0 <= delta or bernoulli_distribution(exp(BOLTZMANN * delta) * temperature)(gen)) {
                score = next_score;
                cur = nxt;
                used = next_used;
                placed_small.clear();
                placed_large.clear();
                used_t0 = set<int>();
                REP (j, 2 * K) if (cur[j].first != -1) {
                    (j < K ? placed_small : placed_large).push_back(j);
                    used_t0.insert(cur[j].first);
                }
                if (highscore < score) {
                    highscore = score;
                    result = cur;
                }
            }


        } else {
            int i = sample1(ALL(puttable_i), gen);
            int y, x; tie(y, x) = sample1(ALL(puttable_pos[i]), gen);
            int t0 = puttable_t[i][y][x];
            if (used_t0.count(t0)) ++ t0;
            use(i, t0, y, x);
        }
    }

#ifdef LOCAL
if (stage.turn() == 3) cerr << "highscore = " << score << endl;
if (stage.turn() == 3) {
    REP (y, H) {
        REP (x, W) {
            if (used[y][x] != -1) {
                if (cur[used[y][x]].first >= 0x10) {
                    fprintf(stderr, "z");
                } else {
                    fprintf(stderr, "%x", cur[used[y][x]].first);
                }
            } else if (rest_heat_turn[y][x]) {
                fprintf(stderr, "#");
            } else {
                fprintf(stderr, ".");
            }
        }
        cerr << endl;
    }
}
#endif

#ifdef LOCAL
    REP (i, 2 * K) if (cur[i].first != -1) {
        score += get_score_delta_unput(cur, used, i);
        unput(cur, used, i);
    }
    assert (abs(score) < 1e-8);
#endif
    vector<pair<int, Action> > actions;
    REP (i, 2 * K) if (result[i].first != -1) {
        int t = result[i].first + stage.turn();
        actions.emplace_back(t, result[i].second);
    }
    sort(ALL(actions), [&](pair<int, Action> const & a, pair<int, Action> const & b) {
        return a.first < b.first;
    });
    return actions;
}

int get_next_index(int removed, int i) {
    assert (i != removed);
    return i < removed ? i : i - 1;
}
Action get_action_with_next_index(CandidateLaneType lane_type, int i, Action const & action) {
    if (action.isWaiting() or action.candidateLaneType() != lane_type) return action;
    return Action::Put(
            action.candidateLaneType(),
            get_next_index(i, action.pieceIndex()),
            action.putPos());
}

class solver {
    vector<pair<int, Action> > actions;

public:
    Stage const & stage;
    solver(Stage const & stage_)
            : stage(stage_) {
    }

    Action decide_next_action(Stage const & stage_) {
        assert (&stage == &stage_);

        actions = do_simulated_annealing(stage, actions);
        assert (actions.empty() or actions.front().first >= stage.turn());
        if (not actions.empty() and actions.front().first == stage.turn()) {
            auto action = actions.front().second;
            actions.erase(actions.begin());
            for (auto & it : actions) {
                it.second = get_action_with_next_index(action.candidateLaneType(), action.pieceIndex(), it.second);
            }
            return action;
        }

        return Action::Wait();
    }
};

solver *g_solver = nullptr;
#ifdef LOCAL
int g_stage = 0;
int g_score = 0;
#endif


//------------------------------------------------------------------------------
/// コンストラクタ。
/// @detail 最初のステージ開始前に実行したい処理があればここに書きます。
Answer::Answer()
{
}

//------------------------------------------------------------------------------
/// デストラクタ。
/// @detail 最後のステージ終了後に実行したい処理があればここに書きます。
Answer::~Answer()
{
}

//------------------------------------------------------------------------------
/// 各ステージ開始時に呼び出される処理。
/// @detail 各ステージに対する初期化処理が必要ならここに書きます。
/// @param aStage 現在のステージ。
void Answer::init(const Stage& aStage)
{
#ifdef LOCAL
    cerr << "[*] stage = " << (g_stage ++) << endl;
    g_score = 0;
#endif
    g_solver = new solver(aStage);
}

//------------------------------------------------------------------------------
/// このターンでの行動を指定する。
/// @detail 希望する行動を Action の static 関数で生成して return してください。
///         正常ではない行動を return した場合、何も起きません。
///         詳細は Action のヘッダを参照してください。
/// @param aStage 現在のステージ。
Action Answer::decideNextAction(const Stage& aStage)
{
#ifdef LOCAL
    for (auto const & piece : aStage.oven().lastBakedPieces()) {
        g_score += piece.score();
    }
    if (aStage.turn() % 50 == 0 or aStage.turn() >= 999) {
        cerr << "[*] turn = " << aStage.turn() << ": score = " << g_score << endl;
    }
#endif
    auto action = g_solver->decide_next_action(aStage);
    if (not action.isWaiting()) {
        auto const & piece = get_piece_from_action(aStage, action);
        assert (aStage.oven().isAbleToPut(piece, action.putPos()));
    }
    return action;
}

//------------------------------------------------------------------------------
/// 各ステージ終了時に呼び出される処理。
/// @detail 各ステージに対する終了処理が必要ならここに書きます。
/// @param aStage 現在のステージ。
void Answer::finalize(const Stage& aStage)
{
    delete g_solver;
    g_solver = nullptr;
}

} // namespace
// EOF
