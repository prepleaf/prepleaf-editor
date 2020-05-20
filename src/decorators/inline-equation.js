import React from 'react';
const inlineEquationRegex = /\\ie (.*?) \\ie/g;

function findWithRegex(regex, contentBlock, callback) {
	const text = contentBlock.getText();
	let matchArr, start;
	while ((matchArr = regex.exec(text)) !== null) {
		start = matchArr.index;
		callback(start, start + matchArr[0].length);
	}
}

const strategy = (contentBlock, callback, contentState) => {
	return findWithRegex(inlineEquationRegex, contentBlock, callback);
};
const InlineEquation = ({
	blockKey,
	contentState,
	decoratedText,
	children,
}) => {
	console.log('yoyoyo');
	console.log(decoratedText);
	const matchResult = inlineEquationRegex.exec(decoratedText);
	const matchedText = matchResult && matchResult[1];
	// console.log(inlineEquationRegex.exec(decoratedText));
	return <span style={{ backgroundColor: 'red' }}>{children}</span>;
};
export default { strategy, component: InlineEquation };
