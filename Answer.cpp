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

void fill_puttable_t(Stage const & stage, array<array<array<int16_t, W>, H>, K> & puttable_t) {
    // TODO: O(KHWb) から O(Kb + KHW) にできる
    REP (i, K) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
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

void list_puttable_pos(Stage const & stage, array<array<array<int16_t, W>, H>, K> const & puttable_t, int DEPTH, array<vector<pair<int8_t, int8_t> >, K> & puttable_pos) {
    REP (i, K) {
        puttable_pos[i].clear();
        REP (y, H) REP (x, W) {
            if (puttable_t[i][y][x] < DEPTH) {
                puttable_pos[i].emplace_back(y, x);
            }
        }
    }
}

vector<pair<int, Action> > do_large_simulated_annealing(Stage const & stage) {
    constexpr int DEPTH = 20;
#ifdef LOCAL
    random_device device;
    static xor_shift_128 gen((device()));
#else
    static xor_shift_128 gen;
#endif

    static array<array<int16_t, W>, H> rest_heat_turn;
    fill_rest_hest_turn(stage.oven(), rest_heat_turn);

    static array<array<array<int16_t, W>, H>, K> puttable_t;
    fill_puttable_t(stage, puttable_t);

    static array<vector<pair<int8_t, int8_t> >, K> puttable_pos;
    list_puttable_pos(stage, puttable_t, DEPTH, puttable_pos);

    vector<int> puttable_i;
    REP (i, K) if (not puttable_pos[i].empty()) {
        puttable_i.push_back(i);
    }
    if (puttable_i.empty()) {
        return vector<pair<int, Action> >();
    }

    auto get_score_delta_one = [&](array<pair<int, Action>, K> const & cur, array<array<int8_t, H>, W> const & used, array<bool, K> const & removed, int i, int ly, int lx) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        int t0 = puttable_t[i][ly][lx];
        int t = piece.requiredHeatTurnCount();
        auto touch = [&](int y, int x) -> double {
            if (not is_on_oven(y, x)) return t;
            double acc = 0;
            if (rest_heat_turn[y][x]) {
                acc += max(0, min<int>(rest_heat_turn[y][x], t + t0) - t0);
            }
            int j = used[y][x];
            if (j != -1 and not removed[j]) {
                auto const & piece_ = stage.candidateLane(CandidateLaneType_Large).pieces()[j];
                int t0_ = cur[j].first;
                int t_ = piece_.requiredHeatTurnCount();
                int a = max(0, min(t0 + t, t0_ + t_) - max(t0, t0_));
                int b = abs((t0 + t) - (t0_ + t_)) + abs(t0 - t0_);
                acc += exp(- t0_ / 2.0) * max(1.0, a - 0.5 * b);
            }
            return acc;
        };
        double score = 0;
        score += pow(piece.height() * piece.width(), 1.5);
        if (lx == 0) score += t * (ry - ly);
        if (lx != 0) REP3 (y, ly, ry) touch(y, lx - 1);
        if (ly == 0) score += t * (rx - lx);
        if (ly != 0) REP3 (x, lx, rx) touch(ly - 1, x);
        if (rx == W) score += t * (ry - ly);
        if (rx != W) REP3 (y, ly, ry) touch(y, rx);
        if (ry == H) score += t * (rx - lx);
        if (ry != H) REP3 (x, lx, rx) touch(ry, x);
        return exp(- t0 / 2.0) * score;
    };

    auto get_score_delta_unput = [&](array<pair<int, Action>, K> const & cur, array<array<int8_t, H>, W> const & used, int i) {
        assert (cur[i].first != -1);
        array<bool, K> removed = {};
        auto const & pos = cur[i].second.putPos();
        return - get_score_delta_one(cur, used, removed, i, pos.y, pos.x);
    };

    auto get_score_delta_put = [&](array<pair<int, Action>, K> const & cur, array<array<int8_t, H>, W> const & used, int i, int y, int x) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
        double score = 0;
        array<bool, K> removed = {};
        REP (j, K) if (cur[j].first != -1) {
            auto const & action = cur[j].second;
            if (j == i or is_intersect(Vector2i(x, y), piece, action.putPos(), get_piece_from_action(stage, action))) {
                removed[j] = true;
                score -= get_score_delta_one(cur, used, removed, j, action.putPos().y, action.putPos().x);
            }
        }
        score += get_score_delta_one(cur, used, removed, i, y, x);
        return score;
    };

    auto unput = [&](array<pair<int, Action>, K> & cur, array<array<int8_t, H>, W> & used, int i) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
        int ly = cur[i].second.putPos().y;
        int lx = cur[i].second.putPos().x;
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        REP3 (y, ly, ry) REP3 (x, lx, rx) {
            used[y][x] = -1;
        }
        cur[i].first = -1;
    };

    auto put = [&](array<pair<int, Action>, K> & cur, array<array<int8_t, H>, W> & used, int i, int ly, int lx) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
        if (cur[i].first != -1) {
            unput(cur, used, i);
        }
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        REP3 (y, ly, ry) REP3 (x, lx, rx) {
            if (used[y][x] != -1) {
                unput(cur, used, used[y][x]);
            }
            used[y][x] = i;
        }
        cur[i].first = puttable_t[i][ly][lx];
        cur[i].second = Action::Put(CandidateLaneType_Large, i, Vector2i(lx, ly));
    };

    array<pair<int, Action>, K> cur;
    fill(ALL(cur), make_pair(-1, Action::Wait()));
    double score = 0;
    array<array<int8_t, H>, W> used = {};
    REP (y, H) REP (x, W) used[y][x] = -1;

    auto result = cur;
    auto highscore = score;
    constexpr int ITERATION = 2048;
    REP (iteration, ITERATION) {

        int i = sample1(ALL(puttable_i), gen);
        shuffle(ALL(puttable_pos[i]), gen);
        for (auto const & pos : puttable_pos[i]) {
            int y, x; tie(y, x) = pos;

            auto delta = get_score_delta_put(cur, used, i, y, x);
            double temperature = (double)(ITERATION - iteration) / ITERATION;
            constexpr double BOLTZMANN = 0.01;
            if (0 <= delta or bernoulli_distribution(exp(BOLTZMANN * delta / temperature))(gen)) {
                score += delta;
                put(cur, used, i, y, x);
                if (highscore < score) {
                    highscore = score;
                    result = cur;
                }
                break;
            }
        }
    }

    REP (i, K) if (cur[i].first != -1) {
        score += get_score_delta_unput(cur, used, i);
        unput(cur, used, i);
    }
#ifdef LOCAL
    assert (abs(score) < 1e-8);
#endif
    vector<pair<double, int> > order;
    REP (i, K) if (result[i].first != -1) {
        auto const & pos = result[i].second.putPos();
        double score_i = get_score_delta_put(cur, used, i, pos.y, pos.x);
        order.emplace_back(score_i, i);
    }
    vector<pair<int, Action> > actions;
    set<int> fixed_turn;
    sort(order.rbegin(), order.rend());
    for (auto it : order) {
        int i = it.second;
        int turn = stage.turn() + result[i].first;
        while (fixed_turn.count(turn)) ++ turn;
        fixed_turn.insert(turn);
        actions.emplace_back(turn, result[i].second);
    }
    return actions;
}

Action do_small_greedy(Stage const & stage, vector<pair<int, Action> > const & actions) {
    array<int, Parameter::CandidatePieceCount> order;
    iota(ALL(order), 0);
    sort(ALL(order), [&](int i, int j) {
        auto const & p = stage.candidateLane(CandidateLaneType_Small).pieces()[i];
        auto const & q = stage.candidateLane(CandidateLaneType_Small).pieces()[j];
        return p.height() * p.width() > q.height() * q.width();
    });
    for (int i : order) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Small).pieces()[i];
        bool found = false;
        Vector2i found_pos;
        iterate_all_puttable_pos(stage.oven(), piece, [&](Vector2i const & pos) {
            if (found) return;

            // 大型クッキーの予定と整合するか確認
            for (auto const & it : actions) {
                if (stage.turn() + piece.requiredHeatTurnCount() < it.first) break;
                auto const & action = it.second;
                if (is_intersect(pos, piece, action.putPos(), get_piece_from_action(stage, action))) {
                    return;
                }
            }

            found = true;
            found_pos = pos;
        });

        if (found) {
            return Action::Put(CandidateLaneType_Small, i, found_pos);
        }
    }

    return Action::Wait();
}

class solver {
    packed_oven_t last_oven;
    int actions_turn;
    vector<pair<int, Action> > actions;

public:
    Stage const & stage;
    solver(Stage const & stage_)
            : stage(stage_) {
        last_oven = pack_oven(stage_.oven());
        actions_turn = -1;
    }

    Action decide_next_action(Stage const & stage_) {
        assert (&stage == &stage_);

        // // 状況が変わってないなら省略
        // if (not stage_.oven().isEmpty()) {
        //     auto packed_oven = pack_oven(stage_.oven());
        //     if (packed_oven == last_oven) {
        //         return Action::Wait();
        //     }
        //     last_oven = packed_oven;
        // }

        // // 置けるやつがひとつもないなら省略
        // bool is_puttable = false;
        // for (auto lane_type : { CandidateLaneType_Large, CandidateLaneType_Small }) {
        //     REP (i, Parameter::CandidatePieceCount) {
        //         if (is_puttable) break;
        //         auto const & piece = stage.candidateLane(lane_type).pieces()[i];
        //         iterate_all_puttable_pos(stage.oven(), piece, [&](Vector2i const & pos) {
        //             is_puttable = true;
        //         });
        //     }
        // }
        // if (not is_puttable) {
        //     return Action::Wait();
        // }

        // 大型クッキーについて焼き鈍し
        if (actions_turn == -1 or stage.turn() > actions_turn + 8) {
            actions_turn = stage.turn();
            actions = do_large_simulated_annealing(stage);
        }
        assert (actions.empty() or actions.front().first >= stage.turn());
        if (not actions.empty() and actions.front().first == stage.turn()) {
            auto action = actions.front().second;
            actions_turn = -1;
            actions.clear();
            return action;
        }

        // 小型クッキーは貪欲
        auto action = do_small_greedy(stage, actions);
        if (not action.isWaiting()) return action;

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
