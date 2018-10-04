//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once

//------------------------------------------------------------------------------
#include "Array.hpp"
#include "OvenRecipe.hpp"
#include "Parameter.hpp"
#include "Piece.hpp"
#include "Vector2i.hpp"

//------------------------------------------------------------------------------
namespace hpc {

/// オーブンの動作に関連する生地の配列。
using OvenedPieces = Array<Piece, Parameter::OvenCellCount>;

/// 生地を焼成する装置、オーブン。
class Oven
{
public:
    /// @name コンストラクタ
    //@{
    Oven();
    explicit Oven(const OvenRecipe& aRecipe);
    //@}

    /// @name 配置問い合わせ
    /// @detail 「生地を pos の位置に配置する」ということが
    ///         どういう配置を意味するかは Piece::pos の説明を参照してください。
    //@{
    /// 生地を指定した場所に配置できるか？
    /// @detail 「配置できる」とは
    ///         「生地をそこに配置したとき、オーブンの天板の範囲に収まっていて
    ///          かつ他の配置済みの生地と被らない」という意味です。
    /// @param aPiece 配置したい生地。
    /// @param aPos 配置したい場所。
    /// @return 配置できるなら true 。
    bool isAbleToPut(const Piece& aPiece, const Vector2i& aPos) const;
    /// 生地を指定した場所に配置できるか？
    /// @detail 「配置できる」とは
    ///         「生地をそこに配置したとき、オーブンの天板の範囲に収まっていて
    ///          かつ他の配置済みの生地と被らない」という意味です。
    /// @param aPieceWidth 配置したい生地の横幅。
    /// @param aPieceHeight 配置したい生地の縦幅。
    /// @param aPos 配置したい場所。
    /// @return 配置できるなら true 。
    bool isAbleToPut(int aPieceWidth, int aPieceHeight, const Vector2i& aPos) const;
    /// 生地を指定した場所に置いたとき、天板に収まるか？
    /// @param aPiece 配置したい生地。
    /// @param aPos 配置したい場所。
    /// @return 収まるなら true 。
    bool isInArea(const Piece& aPiece, const Vector2i& aPos) const;
    /// 生地を指定した場所に置いたとき、天板に収まるか？
    /// @param aPieceWidth 配置したい生地の横幅。
    /// @param aPieceHeight 配置したい生地の縦幅。
    /// @param aPos 配置したい場所。
    /// @return 収まるなら true 。
    bool isInArea(int aPieceWidth, int aPieceHeight, const Vector2i& aPos) const;
    /// 生地を指定した場所に置いたとき、すでに天板に配置されている他の生地と被るか？
    /// @param aPiece 配置したい生地。
    /// @param aPos 配置したい場所。
    /// @return 被るなら true 。
    bool isIntersectAnyBakingPiece(const Piece& aPiece, const Vector2i& aPos) const;
    /// 生地を指定した場所に置いたとき、すでに天板に配置されている他の生地と被るか？
    /// @param aPieceWidth 配置したい生地の横幅。
    /// @param aPieceHeight 配置したい生地の縦幅。
    /// @param aPos 配置したい場所。
    /// @return 被るなら true 。
    bool isIntersectAnyBakingPiece(
        int aPieceWidth,
        int aPieceHeight,
        const Vector2i& aPos
        ) const;
    //@}

    /// @name 一般的な問い合わせ
    //@{
    /// 天板の横幅。
    int width() const;
    /// 天板の縦幅。
    int height() const;
    /// 天板の面積。
    int area() const;
    /// 天板が空っぽか？
    /// @return 天板に生地が乗っていない状態だったら true
    bool isEmpty() const;
    /// 天板上で現在焼いている最中の生地一覧。
    const OvenedPieces& bakingPieces() const;
    /// 天板上で現在焼いている最中の生地一覧。
    OvenedPieces& bakingPieces();
    /// 直前のターンで焼き上がった生地一覧。
    const OvenedPieces& lastBakedPieces() const;
    /// 直前のターンで焼き上がった生地一覧。
    OvenedPieces& lastBakedPieces();
    //@}

    /// @name シミュレーション
    //@{
    /// オーブンの加熱を1ターンすすめ、焼き上がったものを処分する。
    /// @detail オーブンの動作をシミュレートしたいときに使うことを想定しています。
    void bakeAndDiscard();
    //@}

    /// @name 内部用関数
    //@{
    /// 指定のターン数分、オーブンの加熱時間を進める。
    void addHeatTurnCount(int aTurnCount);
    /// 直前のターンで焼き上がった生地の情報をクリアする。
    void clearLastBakedPieces();
    /// 現時点で焼き上がっている生地を回収する。
    /// @return 回収された生地の個数。
    int gatherBaked();
    /// 指定した生地を指定した位置に配置することを試みる。
    /// @return 配置に成功したら true 。
    ///         そこに生地を配置すると天板をはみ出る、とか、
    ///         他の生地に被ってしまう、という場合は、
    ///         配置に失敗して false が返る。
    bool tryToBake(Piece* aPiece, const Vector2i& aPos);
    //@}

private:
    /// @name プライベートメンバ変数
    //@{
    /// このオーブンの設定
    OvenRecipe mRecipe;
    /// 今焼いている生地一覧
    OvenedPieces mBakingPieces;
    /// 直前のターンで焼き上がった生地一覧
    OvenedPieces mLastBakedPieces;
    //@}
};

} // namespace
// EOF
