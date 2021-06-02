import React from 'react';
import { PrpeleafEditorGlobalContext } from '../contexts';
import './inline-highlighted-text.css';

const inlineEquationRegex = /\[(.*?)\]/g;

export class EditEquation extends React.Component {
	constructor(props, context) {
		super(props, context);
		const value = props.value
			? props.value.substring(1, props.value.length - 1)
			: '';
		this.state = {
			isValid: this.validate(value),
			value: value,
		};
	}
	validate(value = '') {
		let invalid = false;
		try {
			katex.__parse(value);
		} catch (e) {
			invalid = true;
		} finally {
			return !invalid;
		}
	}
	setValue = (value) => {
		this.setState({ value, isValid: this.validate(value, false) });
	};
	handleSubmit = () => {
		this.props.onChange('[' + this.state.value + ']');
	};
	render() {
		const { onCancel, onChange, value: initialValue } = this.props;
		const setValue = this.setValue;
		const { value, isValid } = this.state;

		const content = (
			<div className="pe-portal-root">
				<div className="pe-portal-cntn">
					<div className="pe-portal-cntrhlpr">
						<div className="pe-portal-styler">
							<textarea
								className="pe-portal-textarea"
								onFocus={(e) => e.stopPropagation()}
								onBlur={(e) => e.stopPropagation()}
								type="text"
								value={value}
								onChange={(e) => setValue(e.target.value)}
							/>
							{isValid ? (
								<span style={{ padding: '0 3px', backgroundColor: '#000' }}>
									{value}
								</span>
							) : (
								<div className="pe-portal-error">Invalid Equation</div>
							)}
							<button className="pe-portal-button cancel" onClick={onCancel}>
								Cancel
							</button>
							<button className="pe-portal-button submit" onClick={this.handleSubmit}>
								Change
							</button>
						</div>
					</div>
				</div>
			</div>
		);
		return content;
	}
}

function findWithRegex(regex, contentBlock, callback) {
	const text = contentBlock.getText();
	let matchArr, start;
	while ((matchArr = regex.exec(text)) !== null) {
		start = matchArr.index;
		callback(start, start + matchArr[0].length);
	}
}

const strategy = (contentBlock, callback, contentState) => {
	return findWithRegex(new RegExp(inlineEquationRegex), contentBlock, callback);
};
class InlineHighlightedText extends React.Component {
	static contextType = PrpeleafEditorGlobalContext;
	render() {
		const { decoratedText, children } = this.props;
		const { readOnly } = this.context;

		const matchResult = new RegExp(inlineEquationRegex).exec(decoratedText);
		const matchedText = matchResult && matchResult[1];
		return (
			<span style={{ backgroundColor: '', display: 'inline-block' }}>
				<span
					className={
						'prepleaf-editor-inline-highlighted-text' +
						(readOnly ? ' readonly' : ' editable')
					}
				>
					{matchedText}
				</span>
				<span
					style={{
						width: '0',
						height: 0,
						overflow: 'hidden',
						display: 'inline-block',
					}}
				>
					{children}
				</span>
			</span>
		);
	}
}
export default { strategy, component: InlineHighlightedText };
