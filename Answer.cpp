﻿#include <algorithm>
#include <bitset>
#include <cassert>
#include <climits>
#include <functional>
#include <iostream>
#include <memory>
#include <numeric>
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

uint64_t hash_oven(Oven const & oven) {
    constexpr int H = Parameter::OvenHeight;
    constexpr int W = Parameter::OvenWidth;
#ifdef LOCAL
    // デバッグの都合で bitset を避けたい
    string s(H * W / CHAR_BIT, '\0');
    REP (y, H) REP (x, W) {
        if (oven.isAbleToPut(1, 1, Vector2i(x, y))) {
            int z = y * W + x;
            s[z / 8] |= 1u << (z % 8);
        }
    }
    return hash<string>()(s);
#else
    // ちょっとだけ速い気がする
    bitset<H * W> packed;
    REP (y, H) REP (x, W) {
        if (oven.isAbleToPut(1, 1, Vector2i(x, y))) {
            packed.set(y * W + x);
        }
    }
    return hash<bitset<H * W> >()(packed);
#endif
}

int get_oven_score(Oven const & oven) {
    constexpr int H = Parameter::OvenHeight;
    constexpr int W = Parameter::OvenWidth;
    array<array<int16_t, W>, H> packed = {};
    int score = 0;
    for (auto const & piece : oven.bakingPieces()) {
        int ly = piece.pos().y;
        int lx = piece.pos().x;
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        int16_t t = piece.restRequiredHeatTurnCount();
        assert (t >= 1);
        REP3 (y, ly, ry) packed[y][lx] = t;
        REP3 (x, lx, rx) packed[ly][x] = t;
        if (ly == 0) score += t * (rx - lx);
        if (ry == H) score += t * (rx - lx);
        if (lx == 0) score += t * (ry - ly);
        if (rx == W) score += t * (ry - ly);
        score += 10 * piece.height() * piece.width();
    }
    for (auto const & piece : oven.bakingPieces()) {
        int ly = piece.pos().y;
        int lx = piece.pos().x;
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        int16_t t = piece.restRequiredHeatTurnCount();
        if (rx < W) REP3 (y, ly, ry) {
            score += min(packed[y][rx], t);
        }
        if (ry < H) REP3 (x, lx, rx) {
            score += min(packed[ry][x], t);
        }
    }
    return score;
}

struct piece_index_map_t {
    array<int, Parameter::CandidatePieceCount> given_to_local;
    piece_index_map_t() {
        iota(ALL(given_to_local), 0);
    }
    void use(int i) {
        rotate(given_to_local.begin() + i, given_to_local.begin() + (i + 1), given_to_local.end());
    }
};

struct state_t {
    Oven oven;
    Action action;
    uint8_t used;
    uint8_t opened;
    int turn;
    ll score;
    weak_ptr<state_t> parent;
    shared_ptr<state_t> wait;
    vector<shared_ptr<state_t> > put;
};

Piece const & get_piece_from_action(Stage const & stage, Action const & action) {
    return stage.candidateLane(action.candidateLaneType()).pieces()[action.pieceIndex()];
}

bool is_intersect(Vector2i const & pos1, Piece const & piece1, Vector2i const & pos2, Piece const & piece2) {
    return Util::IsIntersect(
        pos1, piece1.width(), piece1.height(),
        pos2, piece2.width(), piece2.height());
}

shared_ptr<state_t> new_initial_state(Stage const & stage) {
    auto a = make_shared<state_t>();
    a->oven = stage.oven();
    a->action = Action::Wait();
    a->used = 0;
    a->opened = 0;
    REP (i, Parameter::CandidatePieceCount) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
        if (stage.turn() + piece.requiredHeatTurnCount() >= Parameter::GameTurnLimit) {
            a->used |= 1u << i;
        }
    }
    a->turn = stage.turn();
    a->score = 0;
    return a;
}

shared_ptr<state_t> new_next_state(shared_ptr<state_t> const & a, Stage const & stage, Action const & action) {
    auto b = make_shared<state_t>();
    b->oven = a->oven;
    b->action = action;
    b->used = a->used;
    a->opened = 0;
    b->turn = a->turn + 1;
    b->score = a->score;

    // 紐付ける
    b->parent = a;
    if (action.isWaiting()) {
        assert (not a->wait);
        a->wait = b;
    } else {
        a->put.push_back(b);
    }

    if (not action.isWaiting()) {  // 置く
        Piece piece = get_piece_from_action(stage, action);
        bool baked = b->oven.tryToBake(&piece, action.putPos());
        assert (baked);
        b->used |= 1u << action.pieceIndex();
        b->score += 100 * pow(piece.height() * piece.width(), 1.5);
    }

    // 進める
    b->oven.bakeAndDiscard();
    b->score += get_oven_score(b->oven);

    // 腐らせる
    REP (i, Parameter::CandidatePieceCount) if (not (b->used & (1u << i))) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
        if (b->turn + piece.requiredHeatTurnCount() >= Parameter::GameTurnLimit) {
            b->used |= 1u << i;
        }
    }

    return b;
}

shared_ptr<state_t> get_wait_state(shared_ptr<state_t> const & a, Stage const & stage) {
    if (a->wait) {
        return a->wait;
    } else {
        return new_next_state(a, stage, Action::Wait());
    }
}

vector<pair<int, Action> > get_actions_between(shared_ptr<state_t> const & root, shared_ptr<state_t> it) {
    vector<pair<int, Action> > actions;
    while (it != root) {
        if (not it->action.isWaiting()) {
            actions.emplace_back(it->turn - 1, it->action);
        }
        it = it->parent.lock();
    }
    reverse(ALL(actions));
    return actions;
}

shared_ptr<state_t> get_direct_descendant(shared_ptr<state_t> const & root, shared_ptr<state_t> it) {
    assert (it != root);
    assert (it->parent.lock());
    while (it->parent.lock() != root) {
        it = it->parent.lock();
        assert (it->parent.lock());
    }
    return it;
}

template <typename Func>
void iterate_all_puttable_pos(Oven const & oven, Piece const & piece, Func func) {
    constexpr int H = Parameter::OvenHeight;
    constexpr int W = Parameter::OvenWidth;
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
        REP (x, H - piece.width() + 1) {
            imos[y    ][x + 1] += imos[y][x];
            imos[y + 1][x    ] += imos[y][x];
            imos[y + 1][x + 1] -= imos[y][x];
            if (not imos[y][x]) {
                func(Vector2i(x, y));
            }
        }
    }
}

shared_ptr<state_t> do_large_beam_search(Stage const & stage, shared_ptr<state_t> const & root, piece_index_map_t const & piece_index_map) {
    constexpr int BEAM_DEPTH = 10;
    constexpr int BEAM_WIDTH = 7;
    vector<shared_ptr<state_t> > cur, prv;
    array<int, (1 << Parameter::CandidatePieceCount)> used_pieces = {};
    unordered_set<uint64_t> used_oven;

    cur.push_back(root);
    shared_ptr<state_t> best = get_wait_state(root, stage);
    for (int iteration = 0; iteration < BEAM_DEPTH; ++ iteration) {
        // 置いてみる
        cur.swap(prv);
        cur.clear();
        for (auto const & a : prv) {
            cur.push_back(get_wait_state(a, stage));
            REP (i, Parameter::CandidatePieceCount) if (not ((a->used | a->opened) & (1u << piece_index_map.given_to_local[i]))) {
                a->opened |= 1u << piece_index_map.given_to_local[i];
                auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
                iterate_all_puttable_pos(a->oven, piece, [&](Vector2i const & pos) {
                    auto action = Action::Put(CandidateLaneType_Large, i, pos);
                    new_next_state(a, stage, action);
                });
            }
            for (auto b : a->put) {
                cur.push_back(b);
            }
        }

        // 並べ替え
        sort(ALL(cur), [&](shared_ptr<state_t> const & a, shared_ptr<state_t> const & b) {
            return a->score > b->score;
        });
        if (best->score < cur.front()->score) {
            best = cur.front();
        }

        // 重複排除
        cur.swap(prv);
        cur.clear();
        for (auto const & a : prv) {
            if (used_pieces[a->used] >= 2) continue;
            uint64_t hash = hash_oven(a->oven);
            if (used_oven.count(hash)) continue;
            cur.push_back(a);
            used_pieces[a->used] += 1;
            used_oven.insert(hash);
            if (cur.size() >= BEAM_WIDTH) break;
        }
        fill(ALL(used_pieces), 0);
        used_oven.clear();
    }

    return best;
}

Action do_small_greedy(Stage const & stage, vector<pair<int, Action> > const & actions) {
    Action best_action = Action::Wait();
    int best_score = INT_MIN;

    REP (i, Parameter::CandidatePieceCount) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Small).pieces()[i];
        iterate_all_puttable_pos(stage.oven(), piece, [&](Vector2i const & pos) {

            // 大型クッキーの予定と整合するか確認
            for (auto const & it : actions) {
                if (stage.turn() + piece.requiredHeatTurnCount() < it.first) break;
                auto const & action = it.second;
                if (is_intersect(pos, piece, action.putPos(), get_piece_from_action(stage, action))) {
                    return;
                }
            }

            // 置いてみる
            auto action = Action::Put(CandidateLaneType_Small, i, pos);
            Oven oven = stage.oven();
            Piece piece1 = piece;
            bool baked = oven.tryToBake(&piece1, pos);
            assert (baked);
            int score = 0;
            REP (iteration, 5) {
                oven.bakeAndDiscard();
                score += get_oven_score(oven);
            }
            if (best_score < score) {
                best_score = score;
                best_action = action;
            }
        });
    }

    return best_action;
}

class solver {
    shared_ptr<state_t> state;
    piece_index_map_t piece_index_map;
    packed_oven_t last_oven;

public:
    Stage const & stage;
    solver(Stage const & stage_)
            : stage(stage_) {
        last_oven = pack_oven(stage_.oven());
    }

    Action decide_next_action(Stage const & stage_) {
        assert (&stage == &stage_);

        if (not state) {
            state = new_initial_state(stage);
        }

        // 状況が変わってないなら省略
        if (not stage_.oven().isEmpty()) {
            auto packed_oven = pack_oven(stage_.oven());
            if (packed_oven == last_oven) {
                state = get_wait_state(state, stage);
                return Action::Wait();
            }
            last_oven = packed_oven;
        }

        // 置けるやつがひとつもないなら省略
        bool is_puttable = false;
        for (auto lane_type : { CandidateLaneType_Large, CandidateLaneType_Small }) {
            REP (i, Parameter::CandidatePieceCount) {
                if (is_puttable) break;
                auto const & piece = stage.candidateLane(lane_type).pieces()[i];
                iterate_all_puttable_pos(stage.oven(), piece, [&](Vector2i const & pos) {
                    is_puttable = true;
                });
            }
        }
        if (not is_puttable) {
            state = get_wait_state(state, stage);
            return Action::Wait();
        }

        // 大型クッキーについてビームサーチ
        auto desc_state = do_large_beam_search(stage, state, piece_index_map);
        auto actions = get_actions_between(state, desc_state);
        if (not actions.empty() and actions.front().first == stage.turn()) {
            state = get_direct_descendant(state, desc_state);
            piece_index_map.use(actions.front().second.pieceIndex());
            return actions.front().second;
        }

        // 小型クッキーは貪欲
        auto action = do_small_greedy(stage, actions);
        if (not action.isWaiting()) {
            state = nullptr;  // 破棄
            return action;
        }

        state = get_wait_state(state, stage);
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
    return g_solver->decide_next_action(aStage);
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
