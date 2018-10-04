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
namespace hpc {

/// 整数の2次元ベクトル。
class Vector2i
{
public:
    /// @name 生成
    //@{
    /// ゼロベクトルを生成する。
    static Vector2i Zero();
    //@}

    /// @name コンストラクタ
    //@{
    /// ゼロベクトルとして生成するコンストラクタ。
    Vector2i();
    /// 要素を指定して生成するコンストラクタ。
    Vector2i(int aX, int aY);
    //@}

    ///@name 等値比較
    //@{
    /// 2つのベクトルが等しいかを返す。
    bool operator==(const Vector2i& aRhs) const;
    /// ゼロベクトルと等しいかを返す。
    bool isZeroStrict() const;
    /// 2つのベクトルが等しいかを求める。
    bool equals(const Vector2i& aVec) const;
    //@}

    ///@name 四則演算
    //@{
    /// 正負を反転させたベクトルを返す。
    Vector2i operator-() const;
    /// ベクトルを加算し結果を代入する。
    Vector2i& operator+=(const Vector2i& aRhs);
    /// ベクトルを減算し結果を代入する。
    Vector2i& operator-=(const Vector2i& aRhs);
    /// ベクトルの整数倍を計算し結果を代入する。
    Vector2i& operator*=(int aRhs);
    /// 2つのベクトルの和を返す。
    Vector2i operator+(const Vector2i& aRhs) const;
    /// 2つのベクトルの差を返す。
    Vector2i operator-(const Vector2i& aRhs) const;
    /// ベクトルの整数倍を返す。
    Vector2i operator*(int aRhs) const;
    /// 整数のベクトル倍を返す。
    friend Vector2i operator*(int aLhs, const Vector2i& aRhs);
    //@}

    /// @name 選択
    //@{
    /// 指定のベクトルとの各要素の最小値を選択したベクトルを取得する。
    Vector2i min(const Vector2i& aVal) const;
    /// 指定のベクトルとの各要素の最大値を選択したベクトルを取得する。
    Vector2i max(const Vector2i& aVal) const;
    //@}

    /// @name 距離計算
    //@{
    /// ベクトルの長さを求める。
    float length() const;
    /// ベクトルの長さの二乗を求める。
    float squareLength() const;
    /// 与えた点との距離を求める。
    float dist(const Vector2i& aPoint) const;
    /// 与えた点との距離の二乗を求める。
    float squareDist(const Vector2i& aPoint) const;
    //@}

    /// @name メンバ変数
    //@{
    int x;
    int y;
    //@}
};

} // namespace
// EOF
