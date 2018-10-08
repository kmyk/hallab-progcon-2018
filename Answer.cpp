//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#include <algorithm>
#include <cassert>
#include <numeric>
#include <vector>
#include "Answer.hpp"
#define REP(i, n) for (int i = 0; (i) < (int)(n); ++ (i))
#define REP3(i, m, n) for (int i = (m); (i) < (int)(n); ++ (i))
#define REP_R(i, n) for (int i = int(n) - 1; (i) >= 0; -- (i))
#define REP3R(i, m, n) for (int i = int(n) - 1; (i) >= (int)(m); -- (i))
#define ALL(x) begin(x), end(x)

//------------------------------------------------------------------------------
namespace hpc {

using namespace std;

class solver {

public:
    Stage const & stage;
    solver(Stage const & stage_)
            : stage(stage_) {
    }

    Action decide_next_action(Stage const & stage_) {
        // 大きいやつから先に試す
        for (auto lane_type : { CandidateLaneType_Large, CandidateLaneType_Small }) {
            // 焼き終わらないクッキーを確認
            vector<bool> is_tle(Parameter::CandidatePieceCount);
            REP (i, Parameter::CandidatePieceCount) {
                auto const & piece = stage.candidateLane(lane_type).pieces()[i];
                if (stage.turn() + piece.requiredHeatTurnCount() >= Parameter::GameTurnLimit) {
                    is_tle[i] = true;
                }
            }

            // 面積順に整列
            vector<int> order(Parameter::CandidatePieceCount);
            iota(ALL(order), 0);
            sort(ALL(order), [&](int i, int j) {
                if (is_tle[i] != is_tle[j]) return is_tle[i] < is_tle[j];
                auto const & p = stage.candidateLane(lane_type).pieces()[i];
                auto const & q = stage.candidateLane(lane_type).pieces()[j];
                int a = p.width() * p.height();
                int b = q.width() * q.height();
                if (is_tle[i]) return a < b;
                return a > b;
            });

            // 置けそうなら貪欲に置く
            for (int i : order) {
                auto const & piece = stage.candidateLane(lane_type).pieces()[i];
                if (is_tle[i] and lane_type == CandidateLaneType_Large) continue;  // 時間切れしてても小さいやつは次のを開けるために置く
                REP (y, Parameter::OvenHeight) {
                    REP (x, Parameter::OvenWidth) {
                        Vector2i p = (lane_type == CandidateLaneType_Large) ?
                            Vector2i(y, x) :
                            Vector2i(Parameter::OvenHeight - y - 1, Parameter::OvenWidth - x - 1);
                        if (stage.oven().isAbleToPut(piece, p)) {
                            return Action::Put(lane_type, i, p);
                        }
                    }
                }
            }
        }

        // 何もしない
        return Action::Wait();
    }
};

solver *g_solver = nullptr;


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
