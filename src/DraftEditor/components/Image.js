import React from 'react';
import './Image.css';

const Spin = () => {
	return <span className="pe-spinner" />;
};

const Button = (props) => {
	return <button className="pe-try-again-button" {...props} />;
};

class Image extends React.Component {
	constructor(props, context) {
		super(props, context);
		this.state = { imageKey: 1, isLoading: true, hasError: false };
	}
	handleError = (e) => {
		this.setState({ isLoading: false, hasError: true });
		if (this.state.imageKey < 5) {
			this.timeoutId = setTimeout(() => {
				this.setState({
					imageKey: this.state.imageKey + 1,
					hasError: false,
					isLoading: true,
				});
			}, 5000 * this.state.imageKey);
		}
	};
	handleOnLoad = (e) => {
		this.setState({ isLoading: false, isLoaded: true, hasError: false });
	};
	retryNow = (e) => {
		clearTimeout(this.timeoutId);
		this.setState({
			imageKey: this.state.imageKey + 1,
			hasError: false,
			isLoading: true,
		});
	};
	render() {
		const url = this.props.src;
		const { isLoading, hasError } = this.state;
		return (
			<div style={{ textAlign: 'center' }}>
				<div>
					{url ? (
						<>
							<img
								key={this.state.imageKey}
								onError={this.handleError}
								onLoad={this.handleOnLoad}
								alt=""
								style={{ maxWidth: '100%' }}
								src={url}
							/>
							{isLoading ? (
								<div>
									<Spin />
									<div>Loading</div>
								</div>
							) : null}
							{hasError ? (
								<div>
									<div>
										An error occurred while loading image. Please check your internet and
										try again.
									</div>
									<Button onClick={this.retryNow}>Try again</Button>
								</div>
							) : null}
						</>
					) : (
						<span>Image not available</span>
					)}
				</div>
			</div>
		);
	}
}

export default Image;
