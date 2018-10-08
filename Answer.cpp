//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#include <algorithm>
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
    bitset<H * W> packed;
    REP (y, H) REP (x, W) {
        if (oven.isAbleToPut(1, 1, Vector2i(x, y))) {
            packed.set(y * W + x);
        }
    }
    return hash<bitset<H * W> >()(packed);
}

int get_oven_score(Oven const & oven) {
    constexpr int H = Parameter::OvenHeight;
    constexpr int W = Parameter::OvenWidth;
    array<array<int, W>, H> packed = {};
    int score = 0;
    for (auto const & piece : oven.bakingPieces()) {
        int ly = piece.pos().y;
        int lx = piece.pos().x;
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        int t = piece.restRequiredHeatTurnCount();
        REP3 (y, ly, ry) {
            packed[y][lx] = t;
            packed[y][rx - 1] = t;
        }
        REP3 (x, lx, rx) {
            packed[ly][x] = t;
            packed[ry - 1][x] = t;
        }
        score += 100 * piece.height() * piece.width();
    }
    for (auto const & piece : oven.bakingPieces()) {
        int ly = piece.pos().y;
        int lx = piece.pos().x;
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        int t = piece.restRequiredHeatTurnCount();
        REP3 (y, ly, ry) {
            if (lx - 1 >= 0) score -= abs(packed[y][lx - 1] - t);
            if (rx     <  W) score -= abs(packed[y][rx    ] - t);
        }
        REP3 (x, lx, rx) {
            if (ly - 1 >= 0) score -= abs(packed[ly - 1][x] - t);
            if (ry     <  H) score -= abs(packed[ry    ][x] - t);
        }
    }
    return score;
}

struct state_t {
    Oven oven;
    vector<pair<int, Action> > actions;
    array<bool, Parameter::CandidatePieceCount> used;
    int turn;
    double score;
};

void apply_action(shared_ptr<state_t> & a, Stage const & stage, Action const & action) {
    if (not action.isWaiting()) {  // 置く
        a->actions.emplace_back(a->turn, action);
        int i = action.pieceIndex();
        auto piece = stage.candidateLane(action.candidateLaneType()).pieces()[i];
        bool baked = a->oven.tryToBake(&piece, action.putPos());
        assert (baked);
        a->used[i] = true;
    }

    // 進める
    a->turn += 1;
    a->oven.bakeAndDiscard();
    a->score += get_oven_score(a->oven);

    // 腐らせる
    REP (i, Parameter::CandidatePieceCount) if (not a->used[i]) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
        a->used[i] = (a->turn + piece.requiredHeatTurnCount() >= Parameter::GameTurnLimit);
    }
}

shared_ptr<state_t> make_initial_state(Stage const & stage) {
    auto a = make_shared<state_t>();
    a->oven = stage.oven();
    REP (i, Parameter::CandidatePieceCount) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
        a->used[i] = (stage.turn() + piece.requiredHeatTurnCount() >= Parameter::GameTurnLimit);
    }
    a->turn = stage.turn();
    a->score = 0;
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

vector<pair<int, Action> > do_generic_beam_search(Stage const & stage, CandidateLaneType lane_type, vector<pair<int, Action> > const & fixed_actions) {
    constexpr int BEAM_DEPTH = 20;
    constexpr int BEAM_WIDTH = 10;

    vector<shared_ptr<state_t> > cur, prv;
    array<int, (1 << Parameter::CandidatePieceCount)> used_pieces = {};
    unordered_set<uint64_t> used_oven;
    cur.push_back(make_initial_state(stage));
    if (not count(ALL(cur.front()->used), false)) {
        return vector<pair<int, Action> >();
    }
    shared_ptr<state_t> best = cur.front();

    auto fixed = fixed_actions.begin();
    for (int iteration = 0; iteration < BEAM_DEPTH; ++ iteration) {

        if (fixed != fixed_actions.end() and fixed->first == stage.turn() + iteration) {  // 既に置く場所が決まっている
            auto const & action = fixed->second;
            ++ fixed;
            auto const & piece = get_piece_from_action(stage, action);
            for (auto & a : cur) {
                assert (a->oven.isAbleToPut(piece, action.putPos()));
                apply_action(a, stage, action);
            }

        } else {  // 置けるところすべて試しに置いてみる
            cur.swap(prv);
            cur.clear();
            for (auto const & a : prv) {
                REP (i, Parameter::CandidatePieceCount) if (not a->used[i]) {
                    auto const & piece = stage.candidateLane(lane_type).pieces()[i];
                    REP (y, Parameter::OvenHeight) {
                        REP (x, Parameter::OvenWidth) {
                            Vector2i p(x, y);
                            if (not a->oven.isAbleToPut(piece, p)) continue;
                            bool conflicted = false;
                            for (auto it = fixed; it != fixed_actions.end(); ++ it) {
                                if (a->turn + piece.requiredHeatTurnCount() < it->first) break;
                                auto const & action = it->second;
                                auto const & action_piece = stage.candidateLane(action.candidateLaneType()).pieces()[action.pieceIndex()];
                                if (is_intersect(p, piece, action.putPos(), action_piece)) {
                                    conflicted = true;
                                    break;
                                }

                            }
                            if (conflicted) continue;
                            auto action = Action::Put(lane_type, i, p);
                            auto b = make_shared<state_t>(*a);
                            apply_action(b, stage, action);
                            cur.push_back(b);
                        }
                    }
                }
            }
            if (cur.empty()) break;  // まったく置くところないなら終了
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
            uint8_t pieces = 0;
            REP (i, Parameter::CandidatePieceCount) {
                if (a->used[i]) pieces |= 1u << i;
            }
            if (pieces == -1) continue;
            if (used_pieces[pieces] >= 10) continue;
            uint64_t hash = hash_oven(a->oven);
            if (used_oven.count(hash)) continue;
            cur.push_back(a);
            used_pieces[pieces] += 1;
            used_oven.insert(hash);
            if (cur.size() >= BEAM_WIDTH) break;
        }
        fill(ALL(used_pieces), 0);
        used_oven.clear();
    }

    // 結果の取り出し
    return best->actions;
}

class solver {
    packed_oven_t last_oven;

public:
    Stage const & stage;
    solver(Stage const & stage_)
            : stage(stage_) {
        last_oven = pack_oven(stage_.oven());
    }

    Action decide_next_action(Stage const & stage_) {
        assert (&stage == &stage_);

        // 状況が変わってないなら省略
        if (not stage_.oven().isEmpty()) {
            auto packed_oven = pack_oven(stage_.oven());
            if (packed_oven == last_oven) {
                return Action::Wait();
            }
            last_oven = packed_oven;
        }

        // 大型クッキーについてビームサーチ
        vector<pair<int, Action> > actions;
        actions = do_generic_beam_search(stage, CandidateLaneType_Large, actions);
        if (not actions.empty() and actions.front().first == stage.turn()) {
            return actions.front().second;
        }

        // 小型クッキーについて間を埋める
        actions = do_generic_beam_search(stage, CandidateLaneType_Small, actions);
        if (not actions.empty() and actions.front().first == stage.turn()) {
            return actions.front().second;
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
    cerr << "[*] stage = " << (++ g_stage) << endl;
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
    if (aStage.turn() <= 5 or aStage.turn() % 50 == 0 or aStage.turn() >= 998) {
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
